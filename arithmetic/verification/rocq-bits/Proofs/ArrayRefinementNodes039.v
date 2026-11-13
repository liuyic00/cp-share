(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes038.
Lemma node_39000 (s : N.State) (i : N.Inputs) :
  R.v39000 (state s) (inputs i) = Zmod.unsigned (N.v39000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39000 s i)) at 1.
  unfold R.v39000, N.v39000.
  rewrite ?node_38995.
  rewrite ?node_38999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39001 (s : N.State) (i : N.Inputs) :
  R.v39001 (state s) (inputs i) = Zmod.unsigned (N.v39001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39001 s i)) at 1.
  unfold R.v39001, N.v39001.
  unfold R.v6, N.v6.
  rewrite ?node_39000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39002 (s : N.State) (i : N.Inputs) :
  R.v39002 (state s) (inputs i) = Zmod.unsigned (N.v39002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39002 s i)) at 1.
  unfold R.v39002, N.v39002.
  rewrite ?node_6465.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39003 (s : N.State) (i : N.Inputs) :
  R.v39003 (state s) (inputs i) = Zmod.unsigned (N.v39003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39003 s i)) at 1.
  unfold R.v39003, N.v39003.
  unfold R.v6, N.v6.
  rewrite ?node_6556.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39004 (s : N.State) (i : N.Inputs) :
  R.v39004 (state s) (inputs i) = Zmod.unsigned (N.v39004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39004 s i)) at 1.
  unfold R.v39004, N.v39004.
  rewrite ?node_39002.
  rewrite ?node_39003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39005 (s : N.State) (i : N.Inputs) :
  R.v39005 (state s) (inputs i) = Zmod.unsigned (N.v39005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39005 s i)) at 1.
  unfold R.v39005, N.v39005.
  rewrite ?node_39001.
  rewrite ?node_39004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39006 (s : N.State) (i : N.Inputs) :
  R.v39006 (state s) (inputs i) = Zmod.unsigned (N.v39006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39006 s i)) at 1.
  unfold R.v39006, N.v39006.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39007 (s : N.State) (i : N.Inputs) :
  R.v39007 (state s) (inputs i) = Zmod.unsigned (N.v39007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39007 s i)) at 1.
  unfold R.v39007, N.v39007.
  rewrite ?node_6476.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39008 (s : N.State) (i : N.Inputs) :
  R.v39008 (state s) (inputs i) = Zmod.unsigned (N.v39008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39008 s i)) at 1.
  unfold R.v39008, N.v39008.
  unfold R.v6, N.v6.
  rewrite ?node_6472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39009 (s : N.State) (i : N.Inputs) :
  R.v39009 (state s) (inputs i) = Zmod.unsigned (N.v39009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39009 s i)) at 1.
  unfold R.v39009, N.v39009.
  unfold R.v6, N.v6.
  rewrite ?node_6465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39010 (s : N.State) (i : N.Inputs) :
  R.v39010 (state s) (inputs i) = Zmod.unsigned (N.v39010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39010 s i)) at 1.
  unfold R.v39010, N.v39010.
  rewrite ?node_39008.
  rewrite ?node_39009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39011 (s : N.State) (i : N.Inputs) :
  R.v39011 (state s) (inputs i) = Zmod.unsigned (N.v39011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39011 s i)) at 1.
  unfold R.v39011, N.v39011.
  unfold R.v16484, N.v16484.
  rewrite ?node_39010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39012 (s : N.State) (i : N.Inputs) :
  R.v39012 (state s) (inputs i) = Zmod.unsigned (N.v39012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39012 s i)) at 1.
  unfold R.v39012, N.v39012.
  rewrite ?node_39007.
  rewrite ?node_39011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39013 (s : N.State) (i : N.Inputs) :
  R.v39013 (state s) (inputs i) = Zmod.unsigned (N.v39013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39013 s i)) at 1.
  unfold R.v39013, N.v39013.
  unfold R.v6, N.v6.
  rewrite ?node_39012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39014 (s : N.State) (i : N.Inputs) :
  R.v39014 (state s) (inputs i) = Zmod.unsigned (N.v39014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39014 s i)) at 1.
  unfold R.v39014, N.v39014.
  rewrite ?node_6477.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39015 (s : N.State) (i : N.Inputs) :
  R.v39015 (state s) (inputs i) = Zmod.unsigned (N.v39015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39015 s i)) at 1.
  unfold R.v39015, N.v39015.
  unfold R.v6, N.v6.
  rewrite ?node_6584.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39016 (s : N.State) (i : N.Inputs) :
  R.v39016 (state s) (inputs i) = Zmod.unsigned (N.v39016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39016 s i)) at 1.
  unfold R.v39016, N.v39016.
  rewrite ?node_39014.
  rewrite ?node_39015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39017 (s : N.State) (i : N.Inputs) :
  R.v39017 (state s) (inputs i) = Zmod.unsigned (N.v39017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39017 s i)) at 1.
  unfold R.v39017, N.v39017.
  rewrite ?node_39013.
  rewrite ?node_39016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39018 (s : N.State) (i : N.Inputs) :
  R.v39018 (state s) (inputs i) = Zmod.unsigned (N.v39018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39018 s i)) at 1.
  unfold R.v39018, N.v39018.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39019 (s : N.State) (i : N.Inputs) :
  R.v39019 (state s) (inputs i) = Zmod.unsigned (N.v39019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39019 s i)) at 1.
  unfold R.v39019, N.v39019.
  rewrite ?node_6493.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39020 (s : N.State) (i : N.Inputs) :
  R.v39020 (state s) (inputs i) = Zmod.unsigned (N.v39020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39020 s i)) at 1.
  unfold R.v39020, N.v39020.
  rewrite ?node_6489.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39021 (s : N.State) (i : N.Inputs) :
  R.v39021 (state s) (inputs i) = Zmod.unsigned (N.v39021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39021 s i)) at 1.
  unfold R.v39021, N.v39021.
  rewrite ?node_6485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39022 (s : N.State) (i : N.Inputs) :
  R.v39022 (state s) (inputs i) = Zmod.unsigned (N.v39022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39022 s i)) at 1.
  unfold R.v39022, N.v39022.
  unfold R.v6, N.v6.
  rewrite ?node_6481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39023 (s : N.State) (i : N.Inputs) :
  R.v39023 (state s) (inputs i) = Zmod.unsigned (N.v39023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39023 s i)) at 1.
  unfold R.v39023, N.v39023.
  unfold R.v6, N.v6.
  rewrite ?node_6478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39024 (s : N.State) (i : N.Inputs) :
  R.v39024 (state s) (inputs i) = Zmod.unsigned (N.v39024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39024 s i)) at 1.
  unfold R.v39024, N.v39024.
  rewrite ?node_39022.
  rewrite ?node_39023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39025 (s : N.State) (i : N.Inputs) :
  R.v39025 (state s) (inputs i) = Zmod.unsigned (N.v39025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39025 s i)) at 1.
  unfold R.v39025, N.v39025.
  unfold R.v16484, N.v16484.
  rewrite ?node_39024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39026 (s : N.State) (i : N.Inputs) :
  R.v39026 (state s) (inputs i) = Zmod.unsigned (N.v39026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39026 s i)) at 1.
  unfold R.v39026, N.v39026.
  rewrite ?node_39019.
  rewrite ?node_39020.
  rewrite ?node_39021.
  rewrite ?node_39025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39027 (s : N.State) (i : N.Inputs) :
  R.v39027 (state s) (inputs i) = Zmod.unsigned (N.v39027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39027 s i)) at 1.
  unfold R.v39027, N.v39027.
  unfold R.v6, N.v6.
  rewrite ?node_39026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39028 (s : N.State) (i : N.Inputs) :
  R.v39028 (state s) (inputs i) = Zmod.unsigned (N.v39028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39028 s i)) at 1.
  unfold R.v39028, N.v39028.
  rewrite ?node_6494.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39029 (s : N.State) (i : N.Inputs) :
  R.v39029 (state s) (inputs i) = Zmod.unsigned (N.v39029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39029 s i)) at 1.
  unfold R.v39029, N.v39029.
  unfold R.v6, N.v6.
  rewrite ?node_6573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39030 (s : N.State) (i : N.Inputs) :
  R.v39030 (state s) (inputs i) = Zmod.unsigned (N.v39030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39030 s i)) at 1.
  unfold R.v39030, N.v39030.
  unfold R.v6, N.v6.
  rewrite ?node_6592.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39031 (s : N.State) (i : N.Inputs) :
  R.v39031 (state s) (inputs i) = Zmod.unsigned (N.v39031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39031 s i)) at 1.
  unfold R.v39031, N.v39031.
  rewrite ?node_39028.
  rewrite ?node_39029.
  rewrite ?node_39030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39032 (s : N.State) (i : N.Inputs) :
  R.v39032 (state s) (inputs i) = Zmod.unsigned (N.v39032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39032 s i)) at 1.
  unfold R.v39032, N.v39032.
  rewrite ?node_39027.
  rewrite ?node_39031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39033 (s : N.State) (i : N.Inputs) :
  R.v39033 (state s) (inputs i) = Zmod.unsigned (N.v39033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39033 s i)) at 1.
  unfold R.v39033, N.v39033.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39034 (s : N.State) (i : N.Inputs) :
  R.v39034 (state s) (inputs i) = Zmod.unsigned (N.v39034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39034 s i)) at 1.
  unfold R.v39034, N.v39034.
  rewrite ?node_6485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39035 (s : N.State) (i : N.Inputs) :
  R.v39035 (state s) (inputs i) = Zmod.unsigned (N.v39035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39035 s i)) at 1.
  unfold R.v39035, N.v39035.
  unfold R.v6, N.v6.
  rewrite ?node_6481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39036 (s : N.State) (i : N.Inputs) :
  R.v39036 (state s) (inputs i) = Zmod.unsigned (N.v39036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39036 s i)) at 1.
  unfold R.v39036, N.v39036.
  unfold R.v6, N.v6.
  rewrite ?node_6478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39037 (s : N.State) (i : N.Inputs) :
  R.v39037 (state s) (inputs i) = Zmod.unsigned (N.v39037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39037 s i)) at 1.
  unfold R.v39037, N.v39037.
  rewrite ?node_39035.
  rewrite ?node_39036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39038 (s : N.State) (i : N.Inputs) :
  R.v39038 (state s) (inputs i) = Zmod.unsigned (N.v39038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39038 s i)) at 1.
  unfold R.v39038, N.v39038.
  unfold R.v16484, N.v16484.
  rewrite ?node_39037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39039 (s : N.State) (i : N.Inputs) :
  R.v39039 (state s) (inputs i) = Zmod.unsigned (N.v39039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39039 s i)) at 1.
  unfold R.v39039, N.v39039.
  rewrite ?node_39034.
  rewrite ?node_39038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39040 (s : N.State) (i : N.Inputs) :
  R.v39040 (state s) (inputs i) = Zmod.unsigned (N.v39040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39040 s i)) at 1.
  unfold R.v39040, N.v39040.
  unfold R.v6, N.v6.
  rewrite ?node_39039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39041 (s : N.State) (i : N.Inputs) :
  R.v39041 (state s) (inputs i) = Zmod.unsigned (N.v39041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39041 s i)) at 1.
  unfold R.v39041, N.v39041.
  rewrite ?node_6486.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39042 (s : N.State) (i : N.Inputs) :
  R.v39042 (state s) (inputs i) = Zmod.unsigned (N.v39042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39042 s i)) at 1.
  unfold R.v39042, N.v39042.
  unfold R.v6, N.v6.
  rewrite ?node_6573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39043 (s : N.State) (i : N.Inputs) :
  R.v39043 (state s) (inputs i) = Zmod.unsigned (N.v39043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39043 s i)) at 1.
  unfold R.v39043, N.v39043.
  rewrite ?node_39041.
  rewrite ?node_39042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39044 (s : N.State) (i : N.Inputs) :
  R.v39044 (state s) (inputs i) = Zmod.unsigned (N.v39044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39044 s i)) at 1.
  unfold R.v39044, N.v39044.
  rewrite ?node_39040.
  rewrite ?node_39043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39045 (s : N.State) (i : N.Inputs) :
  R.v39045 (state s) (inputs i) = Zmod.unsigned (N.v39045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39045 s i)) at 1.
  unfold R.v39045, N.v39045.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39046 (s : N.State) (i : N.Inputs) :
  R.v39046 (state s) (inputs i) = Zmod.unsigned (N.v39046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39046 s i)) at 1.
  unfold R.v39046, N.v39046.
  rewrite ?node_6493.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39047 (s : N.State) (i : N.Inputs) :
  R.v39047 (state s) (inputs i) = Zmod.unsigned (N.v39047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39047 s i)) at 1.
  unfold R.v39047, N.v39047.
  unfold R.v6, N.v6.
  rewrite ?node_6489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39048 (s : N.State) (i : N.Inputs) :
  R.v39048 (state s) (inputs i) = Zmod.unsigned (N.v39048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39048 s i)) at 1.
  unfold R.v39048, N.v39048.
  unfold R.v6, N.v6.
  rewrite ?node_6486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39049 (s : N.State) (i : N.Inputs) :
  R.v39049 (state s) (inputs i) = Zmod.unsigned (N.v39049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39049 s i)) at 1.
  unfold R.v39049, N.v39049.
  rewrite ?node_39047.
  rewrite ?node_39048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39050 (s : N.State) (i : N.Inputs) :
  R.v39050 (state s) (inputs i) = Zmod.unsigned (N.v39050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39050 s i)) at 1.
  unfold R.v39050, N.v39050.
  unfold R.v16484, N.v16484.
  rewrite ?node_39049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39051 (s : N.State) (i : N.Inputs) :
  R.v39051 (state s) (inputs i) = Zmod.unsigned (N.v39051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39051 s i)) at 1.
  unfold R.v39051, N.v39051.
  rewrite ?node_39046.
  rewrite ?node_39050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39052 (s : N.State) (i : N.Inputs) :
  R.v39052 (state s) (inputs i) = Zmod.unsigned (N.v39052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39052 s i)) at 1.
  unfold R.v39052, N.v39052.
  unfold R.v6, N.v6.
  rewrite ?node_39051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39053 (s : N.State) (i : N.Inputs) :
  R.v39053 (state s) (inputs i) = Zmod.unsigned (N.v39053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39053 s i)) at 1.
  unfold R.v39053, N.v39053.
  rewrite ?node_6494.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39054 (s : N.State) (i : N.Inputs) :
  R.v39054 (state s) (inputs i) = Zmod.unsigned (N.v39054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39054 s i)) at 1.
  unfold R.v39054, N.v39054.
  unfold R.v6, N.v6.
  rewrite ?node_6592.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39055 (s : N.State) (i : N.Inputs) :
  R.v39055 (state s) (inputs i) = Zmod.unsigned (N.v39055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39055 s i)) at 1.
  unfold R.v39055, N.v39055.
  rewrite ?node_39053.
  rewrite ?node_39054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39056 (s : N.State) (i : N.Inputs) :
  R.v39056 (state s) (inputs i) = Zmod.unsigned (N.v39056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39056 s i)) at 1.
  unfold R.v39056, N.v39056.
  rewrite ?node_39052.
  rewrite ?node_39055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39057 (s : N.State) (i : N.Inputs) :
  R.v39057 (state s) (inputs i) = Zmod.unsigned (N.v39057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39057 s i)) at 1.
  unfold R.v39057, N.v39057.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39058 (s : N.State) (i : N.Inputs) :
  R.v39058 (state s) (inputs i) = Zmod.unsigned (N.v39058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39058 s i)) at 1.
  unfold R.v39058, N.v39058.
  rewrite ?node_6556.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39059 (s : N.State) (i : N.Inputs) :
  R.v39059 (state s) (inputs i) = Zmod.unsigned (N.v39059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39059 s i)) at 1.
  unfold R.v39059, N.v39059.
  rewrite ?node_6552.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39060 (s : N.State) (i : N.Inputs) :
  R.v39060 (state s) (inputs i) = Zmod.unsigned (N.v39060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39060 s i)) at 1.
  unfold R.v39060, N.v39060.
  rewrite ?node_6544.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39061 (s : N.State) (i : N.Inputs) :
  R.v39061 (state s) (inputs i) = Zmod.unsigned (N.v39061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39061 s i)) at 1.
  unfold R.v39061, N.v39061.
  unfold R.v6, N.v6.
  rewrite ?node_6536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39062 (s : N.State) (i : N.Inputs) :
  R.v39062 (state s) (inputs i) = Zmod.unsigned (N.v39062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39062 s i)) at 1.
  unfold R.v39062, N.v39062.
  unfold R.v6, N.v6.
  rewrite ?node_6529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39063 (s : N.State) (i : N.Inputs) :
  R.v39063 (state s) (inputs i) = Zmod.unsigned (N.v39063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39063 s i)) at 1.
  unfold R.v39063, N.v39063.
  rewrite ?node_39061.
  rewrite ?node_39062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39064 (s : N.State) (i : N.Inputs) :
  R.v39064 (state s) (inputs i) = Zmod.unsigned (N.v39064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39064 s i)) at 1.
  unfold R.v39064, N.v39064.
  unfold R.v16484, N.v16484.
  rewrite ?node_39063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39065 (s : N.State) (i : N.Inputs) :
  R.v39065 (state s) (inputs i) = Zmod.unsigned (N.v39065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39065 s i)) at 1.
  unfold R.v39065, N.v39065.
  rewrite ?node_39058.
  rewrite ?node_39059.
  rewrite ?node_39060.
  rewrite ?node_39064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39066 (s : N.State) (i : N.Inputs) :
  R.v39066 (state s) (inputs i) = Zmod.unsigned (N.v39066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39066 s i)) at 1.
  unfold R.v39066, N.v39066.
  unfold R.v6, N.v6.
  rewrite ?node_39065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39067 (s : N.State) (i : N.Inputs) :
  R.v39067 (state s) (inputs i) = Zmod.unsigned (N.v39067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39067 s i)) at 1.
  unfold R.v39067, N.v39067.
  rewrite ?node_6557.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39068 (s : N.State) (i : N.Inputs) :
  R.v39068 (state s) (inputs i) = Zmod.unsigned (N.v39068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39068 s i)) at 1.
  unfold R.v39068, N.v39068.
  unfold R.v6, N.v6.
  rewrite ?node_6638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39069 (s : N.State) (i : N.Inputs) :
  R.v39069 (state s) (inputs i) = Zmod.unsigned (N.v39069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39069 s i)) at 1.
  unfold R.v39069, N.v39069.
  unfold R.v6, N.v6.
  rewrite ?node_6667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39070 (s : N.State) (i : N.Inputs) :
  R.v39070 (state s) (inputs i) = Zmod.unsigned (N.v39070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39070 s i)) at 1.
  unfold R.v39070, N.v39070.
  rewrite ?node_39067.
  rewrite ?node_39068.
  rewrite ?node_39069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39071 (s : N.State) (i : N.Inputs) :
  R.v39071 (state s) (inputs i) = Zmod.unsigned (N.v39071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39071 s i)) at 1.
  unfold R.v39071, N.v39071.
  rewrite ?node_39066.
  rewrite ?node_39070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39072 (s : N.State) (i : N.Inputs) :
  R.v39072 (state s) (inputs i) = Zmod.unsigned (N.v39072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39072 s i)) at 1.
  unfold R.v39072, N.v39072.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39073 (s : N.State) (i : N.Inputs) :
  R.v39073 (state s) (inputs i) = Zmod.unsigned (N.v39073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39073 s i)) at 1.
  unfold R.v39073, N.v39073.
  rewrite ?node_6544.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39074 (s : N.State) (i : N.Inputs) :
  R.v39074 (state s) (inputs i) = Zmod.unsigned (N.v39074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39074 s i)) at 1.
  unfold R.v39074, N.v39074.
  unfold R.v6, N.v6.
  rewrite ?node_6536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39075 (s : N.State) (i : N.Inputs) :
  R.v39075 (state s) (inputs i) = Zmod.unsigned (N.v39075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39075 s i)) at 1.
  unfold R.v39075, N.v39075.
  unfold R.v6, N.v6.
  rewrite ?node_6529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39076 (s : N.State) (i : N.Inputs) :
  R.v39076 (state s) (inputs i) = Zmod.unsigned (N.v39076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39076 s i)) at 1.
  unfold R.v39076, N.v39076.
  rewrite ?node_39074.
  rewrite ?node_39075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39077 (s : N.State) (i : N.Inputs) :
  R.v39077 (state s) (inputs i) = Zmod.unsigned (N.v39077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39077 s i)) at 1.
  unfold R.v39077, N.v39077.
  unfold R.v16484, N.v16484.
  rewrite ?node_39076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39078 (s : N.State) (i : N.Inputs) :
  R.v39078 (state s) (inputs i) = Zmod.unsigned (N.v39078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39078 s i)) at 1.
  unfold R.v39078, N.v39078.
  rewrite ?node_39073.
  rewrite ?node_39077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39079 (s : N.State) (i : N.Inputs) :
  R.v39079 (state s) (inputs i) = Zmod.unsigned (N.v39079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39079 s i)) at 1.
  unfold R.v39079, N.v39079.
  unfold R.v6, N.v6.
  rewrite ?node_39078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39080 (s : N.State) (i : N.Inputs) :
  R.v39080 (state s) (inputs i) = Zmod.unsigned (N.v39080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39080 s i)) at 1.
  unfold R.v39080, N.v39080.
  rewrite ?node_6545.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39081 (s : N.State) (i : N.Inputs) :
  R.v39081 (state s) (inputs i) = Zmod.unsigned (N.v39081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39081 s i)) at 1.
  unfold R.v39081, N.v39081.
  unfold R.v6, N.v6.
  rewrite ?node_6638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39082 (s : N.State) (i : N.Inputs) :
  R.v39082 (state s) (inputs i) = Zmod.unsigned (N.v39082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39082 s i)) at 1.
  unfold R.v39082, N.v39082.
  rewrite ?node_39080.
  rewrite ?node_39081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39083 (s : N.State) (i : N.Inputs) :
  R.v39083 (state s) (inputs i) = Zmod.unsigned (N.v39083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39083 s i)) at 1.
  unfold R.v39083, N.v39083.
  rewrite ?node_39079.
  rewrite ?node_39082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39084 (s : N.State) (i : N.Inputs) :
  R.v39084 (state s) (inputs i) = Zmod.unsigned (N.v39084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39084 s i)) at 1.
  unfold R.v39084, N.v39084.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39085 (s : N.State) (i : N.Inputs) :
  R.v39085 (state s) (inputs i) = Zmod.unsigned (N.v39085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39085 s i)) at 1.
  unfold R.v39085, N.v39085.
  rewrite ?node_6556.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39086 (s : N.State) (i : N.Inputs) :
  R.v39086 (state s) (inputs i) = Zmod.unsigned (N.v39086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39086 s i)) at 1.
  unfold R.v39086, N.v39086.
  unfold R.v6, N.v6.
  rewrite ?node_6552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39087 (s : N.State) (i : N.Inputs) :
  R.v39087 (state s) (inputs i) = Zmod.unsigned (N.v39087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39087 s i)) at 1.
  unfold R.v39087, N.v39087.
  unfold R.v6, N.v6.
  rewrite ?node_6545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39088 (s : N.State) (i : N.Inputs) :
  R.v39088 (state s) (inputs i) = Zmod.unsigned (N.v39088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39088 s i)) at 1.
  unfold R.v39088, N.v39088.
  rewrite ?node_39086.
  rewrite ?node_39087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39089 (s : N.State) (i : N.Inputs) :
  R.v39089 (state s) (inputs i) = Zmod.unsigned (N.v39089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39089 s i)) at 1.
  unfold R.v39089, N.v39089.
  unfold R.v16484, N.v16484.
  rewrite ?node_39088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39090 (s : N.State) (i : N.Inputs) :
  R.v39090 (state s) (inputs i) = Zmod.unsigned (N.v39090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39090 s i)) at 1.
  unfold R.v39090, N.v39090.
  rewrite ?node_39085.
  rewrite ?node_39089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39091 (s : N.State) (i : N.Inputs) :
  R.v39091 (state s) (inputs i) = Zmod.unsigned (N.v39091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39091 s i)) at 1.
  unfold R.v39091, N.v39091.
  unfold R.v6, N.v6.
  rewrite ?node_39090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39092 (s : N.State) (i : N.Inputs) :
  R.v39092 (state s) (inputs i) = Zmod.unsigned (N.v39092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39092 s i)) at 1.
  unfold R.v39092, N.v39092.
  rewrite ?node_6557.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39093 (s : N.State) (i : N.Inputs) :
  R.v39093 (state s) (inputs i) = Zmod.unsigned (N.v39093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39093 s i)) at 1.
  unfold R.v39093, N.v39093.
  unfold R.v6, N.v6.
  rewrite ?node_6667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39094 (s : N.State) (i : N.Inputs) :
  R.v39094 (state s) (inputs i) = Zmod.unsigned (N.v39094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39094 s i)) at 1.
  unfold R.v39094, N.v39094.
  rewrite ?node_39092.
  rewrite ?node_39093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39095 (s : N.State) (i : N.Inputs) :
  R.v39095 (state s) (inputs i) = Zmod.unsigned (N.v39095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39095 s i)) at 1.
  unfold R.v39095, N.v39095.
  rewrite ?node_39091.
  rewrite ?node_39094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39096 (s : N.State) (i : N.Inputs) :
  R.v39096 (state s) (inputs i) = Zmod.unsigned (N.v39096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39096 s i)) at 1.
  unfold R.v39096, N.v39096.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39097 (s : N.State) (i : N.Inputs) :
  R.v39097 (state s) (inputs i) = Zmod.unsigned (N.v39097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39097 s i)) at 1.
  unfold R.v39097, N.v39097.
  rewrite ?node_6573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39098 (s : N.State) (i : N.Inputs) :
  R.v39098 (state s) (inputs i) = Zmod.unsigned (N.v39098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39098 s i)) at 1.
  unfold R.v39098, N.v39098.
  rewrite ?node_6569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39099 (s : N.State) (i : N.Inputs) :
  R.v39099 (state s) (inputs i) = Zmod.unsigned (N.v39099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39099 s i)) at 1.
  unfold R.v39099, N.v39099.
  rewrite ?node_6565.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39100 (s : N.State) (i : N.Inputs) :
  R.v39100 (state s) (inputs i) = Zmod.unsigned (N.v39100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39100 s i)) at 1.
  unfold R.v39100, N.v39100.
  unfold R.v6, N.v6.
  rewrite ?node_6561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39101 (s : N.State) (i : N.Inputs) :
  R.v39101 (state s) (inputs i) = Zmod.unsigned (N.v39101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39101 s i)) at 1.
  unfold R.v39101, N.v39101.
  unfold R.v6, N.v6.
  rewrite ?node_6558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39102 (s : N.State) (i : N.Inputs) :
  R.v39102 (state s) (inputs i) = Zmod.unsigned (N.v39102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39102 s i)) at 1.
  unfold R.v39102, N.v39102.
  rewrite ?node_39100.
  rewrite ?node_39101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39103 (s : N.State) (i : N.Inputs) :
  R.v39103 (state s) (inputs i) = Zmod.unsigned (N.v39103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39103 s i)) at 1.
  unfold R.v39103, N.v39103.
  unfold R.v16484, N.v16484.
  rewrite ?node_39102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39104 (s : N.State) (i : N.Inputs) :
  R.v39104 (state s) (inputs i) = Zmod.unsigned (N.v39104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39104 s i)) at 1.
  unfold R.v39104, N.v39104.
  rewrite ?node_39097.
  rewrite ?node_39098.
  rewrite ?node_39099.
  rewrite ?node_39103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39105 (s : N.State) (i : N.Inputs) :
  R.v39105 (state s) (inputs i) = Zmod.unsigned (N.v39105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39105 s i)) at 1.
  unfold R.v39105, N.v39105.
  unfold R.v6, N.v6.
  rewrite ?node_39104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39106 (s : N.State) (i : N.Inputs) :
  R.v39106 (state s) (inputs i) = Zmod.unsigned (N.v39106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39106 s i)) at 1.
  unfold R.v39106, N.v39106.
  rewrite ?node_6574.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39107 (s : N.State) (i : N.Inputs) :
  R.v39107 (state s) (inputs i) = Zmod.unsigned (N.v39107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39107 s i)) at 1.
  unfold R.v39107, N.v39107.
  unfold R.v6, N.v6.
  rewrite ?node_6656.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39108 (s : N.State) (i : N.Inputs) :
  R.v39108 (state s) (inputs i) = Zmod.unsigned (N.v39108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39108 s i)) at 1.
  unfold R.v39108, N.v39108.
  unfold R.v6, N.v6.
  rewrite ?node_6675.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39109 (s : N.State) (i : N.Inputs) :
  R.v39109 (state s) (inputs i) = Zmod.unsigned (N.v39109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39109 s i)) at 1.
  unfold R.v39109, N.v39109.
  rewrite ?node_39106.
  rewrite ?node_39107.
  rewrite ?node_39108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39110 (s : N.State) (i : N.Inputs) :
  R.v39110 (state s) (inputs i) = Zmod.unsigned (N.v39110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39110 s i)) at 1.
  unfold R.v39110, N.v39110.
  rewrite ?node_39105.
  rewrite ?node_39109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39111 (s : N.State) (i : N.Inputs) :
  R.v39111 (state s) (inputs i) = Zmod.unsigned (N.v39111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39111 s i)) at 1.
  unfold R.v39111, N.v39111.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39112 (s : N.State) (i : N.Inputs) :
  R.v39112 (state s) (inputs i) = Zmod.unsigned (N.v39112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39112 s i)) at 1.
  unfold R.v39112, N.v39112.
  rewrite ?node_6565.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39113 (s : N.State) (i : N.Inputs) :
  R.v39113 (state s) (inputs i) = Zmod.unsigned (N.v39113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39113 s i)) at 1.
  unfold R.v39113, N.v39113.
  unfold R.v6, N.v6.
  rewrite ?node_6561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39114 (s : N.State) (i : N.Inputs) :
  R.v39114 (state s) (inputs i) = Zmod.unsigned (N.v39114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39114 s i)) at 1.
  unfold R.v39114, N.v39114.
  unfold R.v6, N.v6.
  rewrite ?node_6558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39115 (s : N.State) (i : N.Inputs) :
  R.v39115 (state s) (inputs i) = Zmod.unsigned (N.v39115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39115 s i)) at 1.
  unfold R.v39115, N.v39115.
  rewrite ?node_39113.
  rewrite ?node_39114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39116 (s : N.State) (i : N.Inputs) :
  R.v39116 (state s) (inputs i) = Zmod.unsigned (N.v39116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39116 s i)) at 1.
  unfold R.v39116, N.v39116.
  unfold R.v16484, N.v16484.
  rewrite ?node_39115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39117 (s : N.State) (i : N.Inputs) :
  R.v39117 (state s) (inputs i) = Zmod.unsigned (N.v39117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39117 s i)) at 1.
  unfold R.v39117, N.v39117.
  rewrite ?node_39112.
  rewrite ?node_39116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39118 (s : N.State) (i : N.Inputs) :
  R.v39118 (state s) (inputs i) = Zmod.unsigned (N.v39118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39118 s i)) at 1.
  unfold R.v39118, N.v39118.
  unfold R.v6, N.v6.
  rewrite ?node_39117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39119 (s : N.State) (i : N.Inputs) :
  R.v39119 (state s) (inputs i) = Zmod.unsigned (N.v39119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39119 s i)) at 1.
  unfold R.v39119, N.v39119.
  rewrite ?node_6566.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39120 (s : N.State) (i : N.Inputs) :
  R.v39120 (state s) (inputs i) = Zmod.unsigned (N.v39120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39120 s i)) at 1.
  unfold R.v39120, N.v39120.
  unfold R.v6, N.v6.
  rewrite ?node_6656.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39121 (s : N.State) (i : N.Inputs) :
  R.v39121 (state s) (inputs i) = Zmod.unsigned (N.v39121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39121 s i)) at 1.
  unfold R.v39121, N.v39121.
  rewrite ?node_39119.
  rewrite ?node_39120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39122 (s : N.State) (i : N.Inputs) :
  R.v39122 (state s) (inputs i) = Zmod.unsigned (N.v39122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39122 s i)) at 1.
  unfold R.v39122, N.v39122.
  rewrite ?node_39118.
  rewrite ?node_39121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39123 (s : N.State) (i : N.Inputs) :
  R.v39123 (state s) (inputs i) = Zmod.unsigned (N.v39123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39123 s i)) at 1.
  unfold R.v39123, N.v39123.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39124 (s : N.State) (i : N.Inputs) :
  R.v39124 (state s) (inputs i) = Zmod.unsigned (N.v39124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39124 s i)) at 1.
  unfold R.v39124, N.v39124.
  rewrite ?node_6573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39125 (s : N.State) (i : N.Inputs) :
  R.v39125 (state s) (inputs i) = Zmod.unsigned (N.v39125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39125 s i)) at 1.
  unfold R.v39125, N.v39125.
  unfold R.v6, N.v6.
  rewrite ?node_6569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39126 (s : N.State) (i : N.Inputs) :
  R.v39126 (state s) (inputs i) = Zmod.unsigned (N.v39126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39126 s i)) at 1.
  unfold R.v39126, N.v39126.
  unfold R.v6, N.v6.
  rewrite ?node_6566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39127 (s : N.State) (i : N.Inputs) :
  R.v39127 (state s) (inputs i) = Zmod.unsigned (N.v39127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39127 s i)) at 1.
  unfold R.v39127, N.v39127.
  rewrite ?node_39125.
  rewrite ?node_39126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39128 (s : N.State) (i : N.Inputs) :
  R.v39128 (state s) (inputs i) = Zmod.unsigned (N.v39128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39128 s i)) at 1.
  unfold R.v39128, N.v39128.
  unfold R.v16484, N.v16484.
  rewrite ?node_39127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39129 (s : N.State) (i : N.Inputs) :
  R.v39129 (state s) (inputs i) = Zmod.unsigned (N.v39129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39129 s i)) at 1.
  unfold R.v39129, N.v39129.
  rewrite ?node_39124.
  rewrite ?node_39128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39130 (s : N.State) (i : N.Inputs) :
  R.v39130 (state s) (inputs i) = Zmod.unsigned (N.v39130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39130 s i)) at 1.
  unfold R.v39130, N.v39130.
  unfold R.v6, N.v6.
  rewrite ?node_39129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39131 (s : N.State) (i : N.Inputs) :
  R.v39131 (state s) (inputs i) = Zmod.unsigned (N.v39131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39131 s i)) at 1.
  unfold R.v39131, N.v39131.
  rewrite ?node_6574.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39132 (s : N.State) (i : N.Inputs) :
  R.v39132 (state s) (inputs i) = Zmod.unsigned (N.v39132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39132 s i)) at 1.
  unfold R.v39132, N.v39132.
  unfold R.v6, N.v6.
  rewrite ?node_6675.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39133 (s : N.State) (i : N.Inputs) :
  R.v39133 (state s) (inputs i) = Zmod.unsigned (N.v39133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39133 s i)) at 1.
  unfold R.v39133, N.v39133.
  rewrite ?node_39131.
  rewrite ?node_39132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39134 (s : N.State) (i : N.Inputs) :
  R.v39134 (state s) (inputs i) = Zmod.unsigned (N.v39134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39134 s i)) at 1.
  unfold R.v39134, N.v39134.
  rewrite ?node_39130.
  rewrite ?node_39133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39135 (s : N.State) (i : N.Inputs) :
  R.v39135 (state s) (inputs i) = Zmod.unsigned (N.v39135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39135 s i)) at 1.
  unfold R.v39135, N.v39135.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39136 (s : N.State) (i : N.Inputs) :
  R.v39136 (state s) (inputs i) = Zmod.unsigned (N.v39136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39136 s i)) at 1.
  unfold R.v39136, N.v39136.
  unfold R.v6, N.v6.
  rewrite ?node_6579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39137 (s : N.State) (i : N.Inputs) :
  R.v39137 (state s) (inputs i) = Zmod.unsigned (N.v39137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39137 s i)) at 1.
  unfold R.v39137, N.v39137.
  unfold R.v6, N.v6.
  rewrite ?node_6578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39138 (s : N.State) (i : N.Inputs) :
  R.v39138 (state s) (inputs i) = Zmod.unsigned (N.v39138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39138 s i)) at 1.
  unfold R.v39138, N.v39138.
  rewrite ?node_39136.
  rewrite ?node_39137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39139 (s : N.State) (i : N.Inputs) :
  R.v39139 (state s) (inputs i) = Zmod.unsigned (N.v39139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39139 s i)) at 1.
  unfold R.v39139, N.v39139.
  unfold R.v16463, N.v16463.
  rewrite ?node_39138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39140 (s : N.State) (i : N.Inputs) :
  R.v39140 (state s) (inputs i) = Zmod.unsigned (N.v39140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39140 s i)) at 1.
  unfold R.v39140, N.v39140.
  rewrite ?node_6580.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39141 (s : N.State) (i : N.Inputs) :
  R.v39141 (state s) (inputs i) = Zmod.unsigned (N.v39141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39141 s i)) at 1.
  unfold R.v39141, N.v39141.
  unfold R.v6, N.v6.
  rewrite ?node_6676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39142 (s : N.State) (i : N.Inputs) :
  R.v39142 (state s) (inputs i) = Zmod.unsigned (N.v39142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39142 s i)) at 1.
  unfold R.v39142, N.v39142.
  rewrite ?node_39140.
  rewrite ?node_39141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39143 (s : N.State) (i : N.Inputs) :
  R.v39143 (state s) (inputs i) = Zmod.unsigned (N.v39143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39143 s i)) at 1.
  unfold R.v39143, N.v39143.
  rewrite ?node_39139.
  rewrite ?node_39142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39144 (s : N.State) (i : N.Inputs) :
  R.v39144 (state s) (inputs i) = Zmod.unsigned (N.v39144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39144 s i)) at 1.
  unfold R.v39144, N.v39144.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39145 (s : N.State) (i : N.Inputs) :
  R.v39145 (state s) (inputs i) = Zmod.unsigned (N.v39145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39145 s i)) at 1.
  unfold R.v39145, N.v39145.
  rewrite ?node_6638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39146 (s : N.State) (i : N.Inputs) :
  R.v39146 (state s) (inputs i) = Zmod.unsigned (N.v39146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39146 s i)) at 1.
  unfold R.v39146, N.v39146.
  rewrite ?node_6634.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39147 (s : N.State) (i : N.Inputs) :
  R.v39147 (state s) (inputs i) = Zmod.unsigned (N.v39147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39147 s i)) at 1.
  unfold R.v39147, N.v39147.
  rewrite ?node_6626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39148 (s : N.State) (i : N.Inputs) :
  R.v39148 (state s) (inputs i) = Zmod.unsigned (N.v39148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39148 s i)) at 1.
  unfold R.v39148, N.v39148.
  unfold R.v6, N.v6.
  rewrite ?node_6618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39149 (s : N.State) (i : N.Inputs) :
  R.v39149 (state s) (inputs i) = Zmod.unsigned (N.v39149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39149 s i)) at 1.
  unfold R.v39149, N.v39149.
  unfold R.v6, N.v6.
  rewrite ?node_6611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39150 (s : N.State) (i : N.Inputs) :
  R.v39150 (state s) (inputs i) = Zmod.unsigned (N.v39150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39150 s i)) at 1.
  unfold R.v39150, N.v39150.
  rewrite ?node_39148.
  rewrite ?node_39149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39151 (s : N.State) (i : N.Inputs) :
  R.v39151 (state s) (inputs i) = Zmod.unsigned (N.v39151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39151 s i)) at 1.
  unfold R.v39151, N.v39151.
  unfold R.v16484, N.v16484.
  rewrite ?node_39150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39152 (s : N.State) (i : N.Inputs) :
  R.v39152 (state s) (inputs i) = Zmod.unsigned (N.v39152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39152 s i)) at 1.
  unfold R.v39152, N.v39152.
  rewrite ?node_39145.
  rewrite ?node_39146.
  rewrite ?node_39147.
  rewrite ?node_39151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39153 (s : N.State) (i : N.Inputs) :
  R.v39153 (state s) (inputs i) = Zmod.unsigned (N.v39153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39153 s i)) at 1.
  unfold R.v39153, N.v39153.
  unfold R.v6, N.v6.
  rewrite ?node_39152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39154 (s : N.State) (i : N.Inputs) :
  R.v39154 (state s) (inputs i) = Zmod.unsigned (N.v39154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39154 s i)) at 1.
  unfold R.v39154, N.v39154.
  rewrite ?node_6639.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39155 (s : N.State) (i : N.Inputs) :
  R.v39155 (state s) (inputs i) = Zmod.unsigned (N.v39155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39155 s i)) at 1.
  unfold R.v39155, N.v39155.
  unfold R.v6, N.v6.
  rewrite ?node_6723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39156 (s : N.State) (i : N.Inputs) :
  R.v39156 (state s) (inputs i) = Zmod.unsigned (N.v39156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39156 s i)) at 1.
  unfold R.v39156, N.v39156.
  unfold R.v6, N.v6.
  rewrite ?node_6754.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39157 (s : N.State) (i : N.Inputs) :
  R.v39157 (state s) (inputs i) = Zmod.unsigned (N.v39157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39157 s i)) at 1.
  unfold R.v39157, N.v39157.
  rewrite ?node_39154.
  rewrite ?node_39155.
  rewrite ?node_39156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39158 (s : N.State) (i : N.Inputs) :
  R.v39158 (state s) (inputs i) = Zmod.unsigned (N.v39158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39158 s i)) at 1.
  unfold R.v39158, N.v39158.
  rewrite ?node_39153.
  rewrite ?node_39157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39159 (s : N.State) (i : N.Inputs) :
  R.v39159 (state s) (inputs i) = Zmod.unsigned (N.v39159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39159 s i)) at 1.
  unfold R.v39159, N.v39159.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39160 (s : N.State) (i : N.Inputs) :
  R.v39160 (state s) (inputs i) = Zmod.unsigned (N.v39160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39160 s i)) at 1.
  unfold R.v39160, N.v39160.
  rewrite ?node_6626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39161 (s : N.State) (i : N.Inputs) :
  R.v39161 (state s) (inputs i) = Zmod.unsigned (N.v39161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39161 s i)) at 1.
  unfold R.v39161, N.v39161.
  unfold R.v6, N.v6.
  rewrite ?node_6618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39162 (s : N.State) (i : N.Inputs) :
  R.v39162 (state s) (inputs i) = Zmod.unsigned (N.v39162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39162 s i)) at 1.
  unfold R.v39162, N.v39162.
  unfold R.v6, N.v6.
  rewrite ?node_6611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39163 (s : N.State) (i : N.Inputs) :
  R.v39163 (state s) (inputs i) = Zmod.unsigned (N.v39163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39163 s i)) at 1.
  unfold R.v39163, N.v39163.
  rewrite ?node_39161.
  rewrite ?node_39162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39164 (s : N.State) (i : N.Inputs) :
  R.v39164 (state s) (inputs i) = Zmod.unsigned (N.v39164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39164 s i)) at 1.
  unfold R.v39164, N.v39164.
  unfold R.v16484, N.v16484.
  rewrite ?node_39163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39165 (s : N.State) (i : N.Inputs) :
  R.v39165 (state s) (inputs i) = Zmod.unsigned (N.v39165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39165 s i)) at 1.
  unfold R.v39165, N.v39165.
  rewrite ?node_39160.
  rewrite ?node_39164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39166 (s : N.State) (i : N.Inputs) :
  R.v39166 (state s) (inputs i) = Zmod.unsigned (N.v39166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39166 s i)) at 1.
  unfold R.v39166, N.v39166.
  unfold R.v6, N.v6.
  rewrite ?node_39165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39167 (s : N.State) (i : N.Inputs) :
  R.v39167 (state s) (inputs i) = Zmod.unsigned (N.v39167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39167 s i)) at 1.
  unfold R.v39167, N.v39167.
  rewrite ?node_6627.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39168 (s : N.State) (i : N.Inputs) :
  R.v39168 (state s) (inputs i) = Zmod.unsigned (N.v39168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39168 s i)) at 1.
  unfold R.v39168, N.v39168.
  unfold R.v6, N.v6.
  rewrite ?node_6723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39169 (s : N.State) (i : N.Inputs) :
  R.v39169 (state s) (inputs i) = Zmod.unsigned (N.v39169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39169 s i)) at 1.
  unfold R.v39169, N.v39169.
  rewrite ?node_39167.
  rewrite ?node_39168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39170 (s : N.State) (i : N.Inputs) :
  R.v39170 (state s) (inputs i) = Zmod.unsigned (N.v39170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39170 s i)) at 1.
  unfold R.v39170, N.v39170.
  rewrite ?node_39166.
  rewrite ?node_39169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39171 (s : N.State) (i : N.Inputs) :
  R.v39171 (state s) (inputs i) = Zmod.unsigned (N.v39171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39171 s i)) at 1.
  unfold R.v39171, N.v39171.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39172 (s : N.State) (i : N.Inputs) :
  R.v39172 (state s) (inputs i) = Zmod.unsigned (N.v39172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39172 s i)) at 1.
  unfold R.v39172, N.v39172.
  rewrite ?node_6638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39173 (s : N.State) (i : N.Inputs) :
  R.v39173 (state s) (inputs i) = Zmod.unsigned (N.v39173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39173 s i)) at 1.
  unfold R.v39173, N.v39173.
  unfold R.v6, N.v6.
  rewrite ?node_6634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39174 (s : N.State) (i : N.Inputs) :
  R.v39174 (state s) (inputs i) = Zmod.unsigned (N.v39174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39174 s i)) at 1.
  unfold R.v39174, N.v39174.
  unfold R.v6, N.v6.
  rewrite ?node_6627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39175 (s : N.State) (i : N.Inputs) :
  R.v39175 (state s) (inputs i) = Zmod.unsigned (N.v39175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39175 s i)) at 1.
  unfold R.v39175, N.v39175.
  rewrite ?node_39173.
  rewrite ?node_39174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39176 (s : N.State) (i : N.Inputs) :
  R.v39176 (state s) (inputs i) = Zmod.unsigned (N.v39176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39176 s i)) at 1.
  unfold R.v39176, N.v39176.
  unfold R.v16484, N.v16484.
  rewrite ?node_39175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39177 (s : N.State) (i : N.Inputs) :
  R.v39177 (state s) (inputs i) = Zmod.unsigned (N.v39177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39177 s i)) at 1.
  unfold R.v39177, N.v39177.
  rewrite ?node_39172.
  rewrite ?node_39176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39178 (s : N.State) (i : N.Inputs) :
  R.v39178 (state s) (inputs i) = Zmod.unsigned (N.v39178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39178 s i)) at 1.
  unfold R.v39178, N.v39178.
  unfold R.v6, N.v6.
  rewrite ?node_39177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39179 (s : N.State) (i : N.Inputs) :
  R.v39179 (state s) (inputs i) = Zmod.unsigned (N.v39179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39179 s i)) at 1.
  unfold R.v39179, N.v39179.
  rewrite ?node_6639.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39180 (s : N.State) (i : N.Inputs) :
  R.v39180 (state s) (inputs i) = Zmod.unsigned (N.v39180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39180 s i)) at 1.
  unfold R.v39180, N.v39180.
  unfold R.v6, N.v6.
  rewrite ?node_6754.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39181 (s : N.State) (i : N.Inputs) :
  R.v39181 (state s) (inputs i) = Zmod.unsigned (N.v39181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39181 s i)) at 1.
  unfold R.v39181, N.v39181.
  rewrite ?node_39179.
  rewrite ?node_39180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39182 (s : N.State) (i : N.Inputs) :
  R.v39182 (state s) (inputs i) = Zmod.unsigned (N.v39182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39182 s i)) at 1.
  unfold R.v39182, N.v39182.
  rewrite ?node_39178.
  rewrite ?node_39181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39183 (s : N.State) (i : N.Inputs) :
  R.v39183 (state s) (inputs i) = Zmod.unsigned (N.v39183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39183 s i)) at 1.
  unfold R.v39183, N.v39183.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39184 (s : N.State) (i : N.Inputs) :
  R.v39184 (state s) (inputs i) = Zmod.unsigned (N.v39184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39184 s i)) at 1.
  unfold R.v39184, N.v39184.
  rewrite ?node_6656.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39185 (s : N.State) (i : N.Inputs) :
  R.v39185 (state s) (inputs i) = Zmod.unsigned (N.v39185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39185 s i)) at 1.
  unfold R.v39185, N.v39185.
  rewrite ?node_6652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39186 (s : N.State) (i : N.Inputs) :
  R.v39186 (state s) (inputs i) = Zmod.unsigned (N.v39186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39186 s i)) at 1.
  unfold R.v39186, N.v39186.
  rewrite ?node_6648.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39187 (s : N.State) (i : N.Inputs) :
  R.v39187 (state s) (inputs i) = Zmod.unsigned (N.v39187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39187 s i)) at 1.
  unfold R.v39187, N.v39187.
  unfold R.v6, N.v6.
  rewrite ?node_6644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39188 (s : N.State) (i : N.Inputs) :
  R.v39188 (state s) (inputs i) = Zmod.unsigned (N.v39188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39188 s i)) at 1.
  unfold R.v39188, N.v39188.
  unfold R.v6, N.v6.
  rewrite ?node_6641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39189 (s : N.State) (i : N.Inputs) :
  R.v39189 (state s) (inputs i) = Zmod.unsigned (N.v39189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39189 s i)) at 1.
  unfold R.v39189, N.v39189.
  rewrite ?node_39187.
  rewrite ?node_39188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39190 (s : N.State) (i : N.Inputs) :
  R.v39190 (state s) (inputs i) = Zmod.unsigned (N.v39190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39190 s i)) at 1.
  unfold R.v39190, N.v39190.
  unfold R.v16484, N.v16484.
  rewrite ?node_39189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39191 (s : N.State) (i : N.Inputs) :
  R.v39191 (state s) (inputs i) = Zmod.unsigned (N.v39191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39191 s i)) at 1.
  unfold R.v39191, N.v39191.
  rewrite ?node_39184.
  rewrite ?node_39185.
  rewrite ?node_39186.
  rewrite ?node_39190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39192 (s : N.State) (i : N.Inputs) :
  R.v39192 (state s) (inputs i) = Zmod.unsigned (N.v39192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39192 s i)) at 1.
  unfold R.v39192, N.v39192.
  unfold R.v6, N.v6.
  rewrite ?node_39191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39193 (s : N.State) (i : N.Inputs) :
  R.v39193 (state s) (inputs i) = Zmod.unsigned (N.v39193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39193 s i)) at 1.
  unfold R.v39193, N.v39193.
  rewrite ?node_6657.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39194 (s : N.State) (i : N.Inputs) :
  R.v39194 (state s) (inputs i) = Zmod.unsigned (N.v39194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39194 s i)) at 1.
  unfold R.v39194, N.v39194.
  unfold R.v6, N.v6.
  rewrite ?node_6741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39195 (s : N.State) (i : N.Inputs) :
  R.v39195 (state s) (inputs i) = Zmod.unsigned (N.v39195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39195 s i)) at 1.
  unfold R.v39195, N.v39195.
  unfold R.v6, N.v6.
  rewrite ?node_6762.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39196 (s : N.State) (i : N.Inputs) :
  R.v39196 (state s) (inputs i) = Zmod.unsigned (N.v39196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39196 s i)) at 1.
  unfold R.v39196, N.v39196.
  rewrite ?node_39193.
  rewrite ?node_39194.
  rewrite ?node_39195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39197 (s : N.State) (i : N.Inputs) :
  R.v39197 (state s) (inputs i) = Zmod.unsigned (N.v39197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39197 s i)) at 1.
  unfold R.v39197, N.v39197.
  rewrite ?node_39192.
  rewrite ?node_39196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39198 (s : N.State) (i : N.Inputs) :
  R.v39198 (state s) (inputs i) = Zmod.unsigned (N.v39198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39198 s i)) at 1.
  unfold R.v39198, N.v39198.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39199 (s : N.State) (i : N.Inputs) :
  R.v39199 (state s) (inputs i) = Zmod.unsigned (N.v39199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39199 s i)) at 1.
  unfold R.v39199, N.v39199.
  rewrite ?node_6648.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39200 (s : N.State) (i : N.Inputs) :
  R.v39200 (state s) (inputs i) = Zmod.unsigned (N.v39200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39200 s i)) at 1.
  unfold R.v39200, N.v39200.
  unfold R.v6, N.v6.
  rewrite ?node_6644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39201 (s : N.State) (i : N.Inputs) :
  R.v39201 (state s) (inputs i) = Zmod.unsigned (N.v39201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39201 s i)) at 1.
  unfold R.v39201, N.v39201.
  unfold R.v6, N.v6.
  rewrite ?node_6641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39202 (s : N.State) (i : N.Inputs) :
  R.v39202 (state s) (inputs i) = Zmod.unsigned (N.v39202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39202 s i)) at 1.
  unfold R.v39202, N.v39202.
  rewrite ?node_39200.
  rewrite ?node_39201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39203 (s : N.State) (i : N.Inputs) :
  R.v39203 (state s) (inputs i) = Zmod.unsigned (N.v39203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39203 s i)) at 1.
  unfold R.v39203, N.v39203.
  unfold R.v16484, N.v16484.
  rewrite ?node_39202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39204 (s : N.State) (i : N.Inputs) :
  R.v39204 (state s) (inputs i) = Zmod.unsigned (N.v39204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39204 s i)) at 1.
  unfold R.v39204, N.v39204.
  rewrite ?node_39199.
  rewrite ?node_39203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39205 (s : N.State) (i : N.Inputs) :
  R.v39205 (state s) (inputs i) = Zmod.unsigned (N.v39205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39205 s i)) at 1.
  unfold R.v39205, N.v39205.
  unfold R.v6, N.v6.
  rewrite ?node_39204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39206 (s : N.State) (i : N.Inputs) :
  R.v39206 (state s) (inputs i) = Zmod.unsigned (N.v39206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39206 s i)) at 1.
  unfold R.v39206, N.v39206.
  rewrite ?node_6649.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39207 (s : N.State) (i : N.Inputs) :
  R.v39207 (state s) (inputs i) = Zmod.unsigned (N.v39207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39207 s i)) at 1.
  unfold R.v39207, N.v39207.
  unfold R.v6, N.v6.
  rewrite ?node_6741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39208 (s : N.State) (i : N.Inputs) :
  R.v39208 (state s) (inputs i) = Zmod.unsigned (N.v39208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39208 s i)) at 1.
  unfold R.v39208, N.v39208.
  rewrite ?node_39206.
  rewrite ?node_39207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39209 (s : N.State) (i : N.Inputs) :
  R.v39209 (state s) (inputs i) = Zmod.unsigned (N.v39209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39209 s i)) at 1.
  unfold R.v39209, N.v39209.
  rewrite ?node_39205.
  rewrite ?node_39208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39210 (s : N.State) (i : N.Inputs) :
  R.v39210 (state s) (inputs i) = Zmod.unsigned (N.v39210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39210 s i)) at 1.
  unfold R.v39210, N.v39210.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39211 (s : N.State) (i : N.Inputs) :
  R.v39211 (state s) (inputs i) = Zmod.unsigned (N.v39211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39211 s i)) at 1.
  unfold R.v39211, N.v39211.
  rewrite ?node_6656.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39212 (s : N.State) (i : N.Inputs) :
  R.v39212 (state s) (inputs i) = Zmod.unsigned (N.v39212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39212 s i)) at 1.
  unfold R.v39212, N.v39212.
  unfold R.v6, N.v6.
  rewrite ?node_6652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39213 (s : N.State) (i : N.Inputs) :
  R.v39213 (state s) (inputs i) = Zmod.unsigned (N.v39213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39213 s i)) at 1.
  unfold R.v39213, N.v39213.
  unfold R.v6, N.v6.
  rewrite ?node_6649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39214 (s : N.State) (i : N.Inputs) :
  R.v39214 (state s) (inputs i) = Zmod.unsigned (N.v39214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39214 s i)) at 1.
  unfold R.v39214, N.v39214.
  rewrite ?node_39212.
  rewrite ?node_39213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39215 (s : N.State) (i : N.Inputs) :
  R.v39215 (state s) (inputs i) = Zmod.unsigned (N.v39215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39215 s i)) at 1.
  unfold R.v39215, N.v39215.
  unfold R.v16484, N.v16484.
  rewrite ?node_39214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39216 (s : N.State) (i : N.Inputs) :
  R.v39216 (state s) (inputs i) = Zmod.unsigned (N.v39216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39216 s i)) at 1.
  unfold R.v39216, N.v39216.
  rewrite ?node_39211.
  rewrite ?node_39215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39217 (s : N.State) (i : N.Inputs) :
  R.v39217 (state s) (inputs i) = Zmod.unsigned (N.v39217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39217 s i)) at 1.
  unfold R.v39217, N.v39217.
  unfold R.v6, N.v6.
  rewrite ?node_39216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39218 (s : N.State) (i : N.Inputs) :
  R.v39218 (state s) (inputs i) = Zmod.unsigned (N.v39218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39218 s i)) at 1.
  unfold R.v39218, N.v39218.
  rewrite ?node_6657.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39219 (s : N.State) (i : N.Inputs) :
  R.v39219 (state s) (inputs i) = Zmod.unsigned (N.v39219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39219 s i)) at 1.
  unfold R.v39219, N.v39219.
  unfold R.v6, N.v6.
  rewrite ?node_6762.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39220 (s : N.State) (i : N.Inputs) :
  R.v39220 (state s) (inputs i) = Zmod.unsigned (N.v39220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39220 s i)) at 1.
  unfold R.v39220, N.v39220.
  rewrite ?node_39218.
  rewrite ?node_39219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39221 (s : N.State) (i : N.Inputs) :
  R.v39221 (state s) (inputs i) = Zmod.unsigned (N.v39221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39221 s i)) at 1.
  unfold R.v39221, N.v39221.
  rewrite ?node_39217.
  rewrite ?node_39220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39222 (s : N.State) (i : N.Inputs) :
  R.v39222 (state s) (inputs i) = Zmod.unsigned (N.v39222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39222 s i)) at 1.
  unfold R.v39222, N.v39222.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39223 (s : N.State) (i : N.Inputs) :
  R.v39223 (state s) (inputs i) = Zmod.unsigned (N.v39223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39223 s i)) at 1.
  unfold R.v39223, N.v39223.
  unfold R.v6, N.v6.
  rewrite ?node_6662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39224 (s : N.State) (i : N.Inputs) :
  R.v39224 (state s) (inputs i) = Zmod.unsigned (N.v39224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39224 s i)) at 1.
  unfold R.v39224, N.v39224.
  unfold R.v6, N.v6.
  rewrite ?node_6661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39225 (s : N.State) (i : N.Inputs) :
  R.v39225 (state s) (inputs i) = Zmod.unsigned (N.v39225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39225 s i)) at 1.
  unfold R.v39225, N.v39225.
  rewrite ?node_39223.
  rewrite ?node_39224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39226 (s : N.State) (i : N.Inputs) :
  R.v39226 (state s) (inputs i) = Zmod.unsigned (N.v39226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39226 s i)) at 1.
  unfold R.v39226, N.v39226.
  unfold R.v16463, N.v16463.
  rewrite ?node_39225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39227 (s : N.State) (i : N.Inputs) :
  R.v39227 (state s) (inputs i) = Zmod.unsigned (N.v39227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39227 s i)) at 1.
  unfold R.v39227, N.v39227.
  rewrite ?node_6663.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39228 (s : N.State) (i : N.Inputs) :
  R.v39228 (state s) (inputs i) = Zmod.unsigned (N.v39228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39228 s i)) at 1.
  unfold R.v39228, N.v39228.
  unfold R.v6, N.v6.
  rewrite ?node_6763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39229 (s : N.State) (i : N.Inputs) :
  R.v39229 (state s) (inputs i) = Zmod.unsigned (N.v39229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39229 s i)) at 1.
  unfold R.v39229, N.v39229.
  rewrite ?node_39227.
  rewrite ?node_39228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39230 (s : N.State) (i : N.Inputs) :
  R.v39230 (state s) (inputs i) = Zmod.unsigned (N.v39230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39230 s i)) at 1.
  unfold R.v39230, N.v39230.
  rewrite ?node_39226.
  rewrite ?node_39229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39231 (s : N.State) (i : N.Inputs) :
  R.v39231 (state s) (inputs i) = Zmod.unsigned (N.v39231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39231 s i)) at 1.
  unfold R.v39231, N.v39231.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39232 (s : N.State) (i : N.Inputs) :
  R.v39232 (state s) (inputs i) = Zmod.unsigned (N.v39232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39232 s i)) at 1.
  unfold R.v39232, N.v39232.
  rewrite ?node_6723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39233 (s : N.State) (i : N.Inputs) :
  R.v39233 (state s) (inputs i) = Zmod.unsigned (N.v39233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39233 s i)) at 1.
  unfold R.v39233, N.v39233.
  rewrite ?node_6719.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39234 (s : N.State) (i : N.Inputs) :
  R.v39234 (state s) (inputs i) = Zmod.unsigned (N.v39234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39234 s i)) at 1.
  unfold R.v39234, N.v39234.
  rewrite ?node_6711.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39235 (s : N.State) (i : N.Inputs) :
  R.v39235 (state s) (inputs i) = Zmod.unsigned (N.v39235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39235 s i)) at 1.
  unfold R.v39235, N.v39235.
  unfold R.v6, N.v6.
  rewrite ?node_6703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39236 (s : N.State) (i : N.Inputs) :
  R.v39236 (state s) (inputs i) = Zmod.unsigned (N.v39236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39236 s i)) at 1.
  unfold R.v39236, N.v39236.
  unfold R.v6, N.v6.
  rewrite ?node_6696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39237 (s : N.State) (i : N.Inputs) :
  R.v39237 (state s) (inputs i) = Zmod.unsigned (N.v39237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39237 s i)) at 1.
  unfold R.v39237, N.v39237.
  rewrite ?node_39235.
  rewrite ?node_39236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39238 (s : N.State) (i : N.Inputs) :
  R.v39238 (state s) (inputs i) = Zmod.unsigned (N.v39238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39238 s i)) at 1.
  unfold R.v39238, N.v39238.
  unfold R.v16484, N.v16484.
  rewrite ?node_39237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39239 (s : N.State) (i : N.Inputs) :
  R.v39239 (state s) (inputs i) = Zmod.unsigned (N.v39239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39239 s i)) at 1.
  unfold R.v39239, N.v39239.
  rewrite ?node_39232.
  rewrite ?node_39233.
  rewrite ?node_39234.
  rewrite ?node_39238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39240 (s : N.State) (i : N.Inputs) :
  R.v39240 (state s) (inputs i) = Zmod.unsigned (N.v39240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39240 s i)) at 1.
  unfold R.v39240, N.v39240.
  unfold R.v6, N.v6.
  rewrite ?node_39239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39241 (s : N.State) (i : N.Inputs) :
  R.v39241 (state s) (inputs i) = Zmod.unsigned (N.v39241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39241 s i)) at 1.
  unfold R.v39241, N.v39241.
  rewrite ?node_6724.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39242 (s : N.State) (i : N.Inputs) :
  R.v39242 (state s) (inputs i) = Zmod.unsigned (N.v39242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39242 s i)) at 1.
  unfold R.v39242, N.v39242.
  unfold R.v6, N.v6.
  rewrite ?node_6812.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39243 (s : N.State) (i : N.Inputs) :
  R.v39243 (state s) (inputs i) = Zmod.unsigned (N.v39243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39243 s i)) at 1.
  unfold R.v39243, N.v39243.
  unfold R.v6, N.v6.
  rewrite ?node_6844.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39244 (s : N.State) (i : N.Inputs) :
  R.v39244 (state s) (inputs i) = Zmod.unsigned (N.v39244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39244 s i)) at 1.
  unfold R.v39244, N.v39244.
  rewrite ?node_39241.
  rewrite ?node_39242.
  rewrite ?node_39243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39245 (s : N.State) (i : N.Inputs) :
  R.v39245 (state s) (inputs i) = Zmod.unsigned (N.v39245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39245 s i)) at 1.
  unfold R.v39245, N.v39245.
  rewrite ?node_39240.
  rewrite ?node_39244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39246 (s : N.State) (i : N.Inputs) :
  R.v39246 (state s) (inputs i) = Zmod.unsigned (N.v39246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39246 s i)) at 1.
  unfold R.v39246, N.v39246.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39247 (s : N.State) (i : N.Inputs) :
  R.v39247 (state s) (inputs i) = Zmod.unsigned (N.v39247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39247 s i)) at 1.
  unfold R.v39247, N.v39247.
  rewrite ?node_6711.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39248 (s : N.State) (i : N.Inputs) :
  R.v39248 (state s) (inputs i) = Zmod.unsigned (N.v39248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39248 s i)) at 1.
  unfold R.v39248, N.v39248.
  unfold R.v6, N.v6.
  rewrite ?node_6703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39249 (s : N.State) (i : N.Inputs) :
  R.v39249 (state s) (inputs i) = Zmod.unsigned (N.v39249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39249 s i)) at 1.
  unfold R.v39249, N.v39249.
  unfold R.v6, N.v6.
  rewrite ?node_6696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39250 (s : N.State) (i : N.Inputs) :
  R.v39250 (state s) (inputs i) = Zmod.unsigned (N.v39250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39250 s i)) at 1.
  unfold R.v39250, N.v39250.
  rewrite ?node_39248.
  rewrite ?node_39249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39251 (s : N.State) (i : N.Inputs) :
  R.v39251 (state s) (inputs i) = Zmod.unsigned (N.v39251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39251 s i)) at 1.
  unfold R.v39251, N.v39251.
  unfold R.v16484, N.v16484.
  rewrite ?node_39250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39252 (s : N.State) (i : N.Inputs) :
  R.v39252 (state s) (inputs i) = Zmod.unsigned (N.v39252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39252 s i)) at 1.
  unfold R.v39252, N.v39252.
  rewrite ?node_39247.
  rewrite ?node_39251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39253 (s : N.State) (i : N.Inputs) :
  R.v39253 (state s) (inputs i) = Zmod.unsigned (N.v39253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39253 s i)) at 1.
  unfold R.v39253, N.v39253.
  unfold R.v6, N.v6.
  rewrite ?node_39252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39254 (s : N.State) (i : N.Inputs) :
  R.v39254 (state s) (inputs i) = Zmod.unsigned (N.v39254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39254 s i)) at 1.
  unfold R.v39254, N.v39254.
  rewrite ?node_6712.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39255 (s : N.State) (i : N.Inputs) :
  R.v39255 (state s) (inputs i) = Zmod.unsigned (N.v39255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39255 s i)) at 1.
  unfold R.v39255, N.v39255.
  unfold R.v6, N.v6.
  rewrite ?node_6812.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39256 (s : N.State) (i : N.Inputs) :
  R.v39256 (state s) (inputs i) = Zmod.unsigned (N.v39256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39256 s i)) at 1.
  unfold R.v39256, N.v39256.
  rewrite ?node_39254.
  rewrite ?node_39255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39257 (s : N.State) (i : N.Inputs) :
  R.v39257 (state s) (inputs i) = Zmod.unsigned (N.v39257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39257 s i)) at 1.
  unfold R.v39257, N.v39257.
  rewrite ?node_39253.
  rewrite ?node_39256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39258 (s : N.State) (i : N.Inputs) :
  R.v39258 (state s) (inputs i) = Zmod.unsigned (N.v39258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39258 s i)) at 1.
  unfold R.v39258, N.v39258.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39259 (s : N.State) (i : N.Inputs) :
  R.v39259 (state s) (inputs i) = Zmod.unsigned (N.v39259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39259 s i)) at 1.
  unfold R.v39259, N.v39259.
  rewrite ?node_6723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39260 (s : N.State) (i : N.Inputs) :
  R.v39260 (state s) (inputs i) = Zmod.unsigned (N.v39260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39260 s i)) at 1.
  unfold R.v39260, N.v39260.
  unfold R.v6, N.v6.
  rewrite ?node_6719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39261 (s : N.State) (i : N.Inputs) :
  R.v39261 (state s) (inputs i) = Zmod.unsigned (N.v39261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39261 s i)) at 1.
  unfold R.v39261, N.v39261.
  unfold R.v6, N.v6.
  rewrite ?node_6712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39262 (s : N.State) (i : N.Inputs) :
  R.v39262 (state s) (inputs i) = Zmod.unsigned (N.v39262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39262 s i)) at 1.
  unfold R.v39262, N.v39262.
  rewrite ?node_39260.
  rewrite ?node_39261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39263 (s : N.State) (i : N.Inputs) :
  R.v39263 (state s) (inputs i) = Zmod.unsigned (N.v39263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39263 s i)) at 1.
  unfold R.v39263, N.v39263.
  unfold R.v16484, N.v16484.
  rewrite ?node_39262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39264 (s : N.State) (i : N.Inputs) :
  R.v39264 (state s) (inputs i) = Zmod.unsigned (N.v39264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39264 s i)) at 1.
  unfold R.v39264, N.v39264.
  rewrite ?node_39259.
  rewrite ?node_39263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39265 (s : N.State) (i : N.Inputs) :
  R.v39265 (state s) (inputs i) = Zmod.unsigned (N.v39265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39265 s i)) at 1.
  unfold R.v39265, N.v39265.
  unfold R.v6, N.v6.
  rewrite ?node_39264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39266 (s : N.State) (i : N.Inputs) :
  R.v39266 (state s) (inputs i) = Zmod.unsigned (N.v39266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39266 s i)) at 1.
  unfold R.v39266, N.v39266.
  rewrite ?node_6724.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39267 (s : N.State) (i : N.Inputs) :
  R.v39267 (state s) (inputs i) = Zmod.unsigned (N.v39267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39267 s i)) at 1.
  unfold R.v39267, N.v39267.
  unfold R.v6, N.v6.
  rewrite ?node_6844.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39268 (s : N.State) (i : N.Inputs) :
  R.v39268 (state s) (inputs i) = Zmod.unsigned (N.v39268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39268 s i)) at 1.
  unfold R.v39268, N.v39268.
  rewrite ?node_39266.
  rewrite ?node_39267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39269 (s : N.State) (i : N.Inputs) :
  R.v39269 (state s) (inputs i) = Zmod.unsigned (N.v39269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39269 s i)) at 1.
  unfold R.v39269, N.v39269.
  rewrite ?node_39265.
  rewrite ?node_39268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39270 (s : N.State) (i : N.Inputs) :
  R.v39270 (state s) (inputs i) = Zmod.unsigned (N.v39270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39270 s i)) at 1.
  unfold R.v39270, N.v39270.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39271 (s : N.State) (i : N.Inputs) :
  R.v39271 (state s) (inputs i) = Zmod.unsigned (N.v39271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39271 s i)) at 1.
  unfold R.v39271, N.v39271.
  rewrite ?node_6741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39272 (s : N.State) (i : N.Inputs) :
  R.v39272 (state s) (inputs i) = Zmod.unsigned (N.v39272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39272 s i)) at 1.
  unfold R.v39272, N.v39272.
  rewrite ?node_6737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39273 (s : N.State) (i : N.Inputs) :
  R.v39273 (state s) (inputs i) = Zmod.unsigned (N.v39273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39273 s i)) at 1.
  unfold R.v39273, N.v39273.
  rewrite ?node_6733.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39274 (s : N.State) (i : N.Inputs) :
  R.v39274 (state s) (inputs i) = Zmod.unsigned (N.v39274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39274 s i)) at 1.
  unfold R.v39274, N.v39274.
  unfold R.v6, N.v6.
  rewrite ?node_6729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39275 (s : N.State) (i : N.Inputs) :
  R.v39275 (state s) (inputs i) = Zmod.unsigned (N.v39275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39275 s i)) at 1.
  unfold R.v39275, N.v39275.
  unfold R.v6, N.v6.
  rewrite ?node_6726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39276 (s : N.State) (i : N.Inputs) :
  R.v39276 (state s) (inputs i) = Zmod.unsigned (N.v39276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39276 s i)) at 1.
  unfold R.v39276, N.v39276.
  rewrite ?node_39274.
  rewrite ?node_39275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39277 (s : N.State) (i : N.Inputs) :
  R.v39277 (state s) (inputs i) = Zmod.unsigned (N.v39277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39277 s i)) at 1.
  unfold R.v39277, N.v39277.
  unfold R.v16484, N.v16484.
  rewrite ?node_39276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39278 (s : N.State) (i : N.Inputs) :
  R.v39278 (state s) (inputs i) = Zmod.unsigned (N.v39278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39278 s i)) at 1.
  unfold R.v39278, N.v39278.
  rewrite ?node_39271.
  rewrite ?node_39272.
  rewrite ?node_39273.
  rewrite ?node_39277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39279 (s : N.State) (i : N.Inputs) :
  R.v39279 (state s) (inputs i) = Zmod.unsigned (N.v39279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39279 s i)) at 1.
  unfold R.v39279, N.v39279.
  unfold R.v6, N.v6.
  rewrite ?node_39278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39280 (s : N.State) (i : N.Inputs) :
  R.v39280 (state s) (inputs i) = Zmod.unsigned (N.v39280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39280 s i)) at 1.
  unfold R.v39280, N.v39280.
  rewrite ?node_6742.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39281 (s : N.State) (i : N.Inputs) :
  R.v39281 (state s) (inputs i) = Zmod.unsigned (N.v39281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39281 s i)) at 1.
  unfold R.v39281, N.v39281.
  unfold R.v6, N.v6.
  rewrite ?node_6831.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39282 (s : N.State) (i : N.Inputs) :
  R.v39282 (state s) (inputs i) = Zmod.unsigned (N.v39282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39282 s i)) at 1.
  unfold R.v39282, N.v39282.
  unfold R.v6, N.v6.
  rewrite ?node_6852.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39283 (s : N.State) (i : N.Inputs) :
  R.v39283 (state s) (inputs i) = Zmod.unsigned (N.v39283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39283 s i)) at 1.
  unfold R.v39283, N.v39283.
  rewrite ?node_39280.
  rewrite ?node_39281.
  rewrite ?node_39282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39284 (s : N.State) (i : N.Inputs) :
  R.v39284 (state s) (inputs i) = Zmod.unsigned (N.v39284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39284 s i)) at 1.
  unfold R.v39284, N.v39284.
  rewrite ?node_39279.
  rewrite ?node_39283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39285 (s : N.State) (i : N.Inputs) :
  R.v39285 (state s) (inputs i) = Zmod.unsigned (N.v39285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39285 s i)) at 1.
  unfold R.v39285, N.v39285.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39286 (s : N.State) (i : N.Inputs) :
  R.v39286 (state s) (inputs i) = Zmod.unsigned (N.v39286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39286 s i)) at 1.
  unfold R.v39286, N.v39286.
  rewrite ?node_6733.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39287 (s : N.State) (i : N.Inputs) :
  R.v39287 (state s) (inputs i) = Zmod.unsigned (N.v39287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39287 s i)) at 1.
  unfold R.v39287, N.v39287.
  unfold R.v6, N.v6.
  rewrite ?node_6729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39288 (s : N.State) (i : N.Inputs) :
  R.v39288 (state s) (inputs i) = Zmod.unsigned (N.v39288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39288 s i)) at 1.
  unfold R.v39288, N.v39288.
  unfold R.v6, N.v6.
  rewrite ?node_6726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39289 (s : N.State) (i : N.Inputs) :
  R.v39289 (state s) (inputs i) = Zmod.unsigned (N.v39289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39289 s i)) at 1.
  unfold R.v39289, N.v39289.
  rewrite ?node_39287.
  rewrite ?node_39288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39290 (s : N.State) (i : N.Inputs) :
  R.v39290 (state s) (inputs i) = Zmod.unsigned (N.v39290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39290 s i)) at 1.
  unfold R.v39290, N.v39290.
  unfold R.v16484, N.v16484.
  rewrite ?node_39289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39291 (s : N.State) (i : N.Inputs) :
  R.v39291 (state s) (inputs i) = Zmod.unsigned (N.v39291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39291 s i)) at 1.
  unfold R.v39291, N.v39291.
  rewrite ?node_39286.
  rewrite ?node_39290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39292 (s : N.State) (i : N.Inputs) :
  R.v39292 (state s) (inputs i) = Zmod.unsigned (N.v39292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39292 s i)) at 1.
  unfold R.v39292, N.v39292.
  unfold R.v6, N.v6.
  rewrite ?node_39291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39293 (s : N.State) (i : N.Inputs) :
  R.v39293 (state s) (inputs i) = Zmod.unsigned (N.v39293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39293 s i)) at 1.
  unfold R.v39293, N.v39293.
  rewrite ?node_6734.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39294 (s : N.State) (i : N.Inputs) :
  R.v39294 (state s) (inputs i) = Zmod.unsigned (N.v39294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39294 s i)) at 1.
  unfold R.v39294, N.v39294.
  unfold R.v6, N.v6.
  rewrite ?node_6831.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39295 (s : N.State) (i : N.Inputs) :
  R.v39295 (state s) (inputs i) = Zmod.unsigned (N.v39295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39295 s i)) at 1.
  unfold R.v39295, N.v39295.
  rewrite ?node_39293.
  rewrite ?node_39294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39296 (s : N.State) (i : N.Inputs) :
  R.v39296 (state s) (inputs i) = Zmod.unsigned (N.v39296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39296 s i)) at 1.
  unfold R.v39296, N.v39296.
  rewrite ?node_39292.
  rewrite ?node_39295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39297 (s : N.State) (i : N.Inputs) :
  R.v39297 (state s) (inputs i) = Zmod.unsigned (N.v39297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39297 s i)) at 1.
  unfold R.v39297, N.v39297.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39298 (s : N.State) (i : N.Inputs) :
  R.v39298 (state s) (inputs i) = Zmod.unsigned (N.v39298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39298 s i)) at 1.
  unfold R.v39298, N.v39298.
  rewrite ?node_6741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39299 (s : N.State) (i : N.Inputs) :
  R.v39299 (state s) (inputs i) = Zmod.unsigned (N.v39299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39299 s i)) at 1.
  unfold R.v39299, N.v39299.
  unfold R.v6, N.v6.
  rewrite ?node_6737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39300 (s : N.State) (i : N.Inputs) :
  R.v39300 (state s) (inputs i) = Zmod.unsigned (N.v39300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39300 s i)) at 1.
  unfold R.v39300, N.v39300.
  unfold R.v6, N.v6.
  rewrite ?node_6734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39301 (s : N.State) (i : N.Inputs) :
  R.v39301 (state s) (inputs i) = Zmod.unsigned (N.v39301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39301 s i)) at 1.
  unfold R.v39301, N.v39301.
  rewrite ?node_39299.
  rewrite ?node_39300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39302 (s : N.State) (i : N.Inputs) :
  R.v39302 (state s) (inputs i) = Zmod.unsigned (N.v39302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39302 s i)) at 1.
  unfold R.v39302, N.v39302.
  unfold R.v16484, N.v16484.
  rewrite ?node_39301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39303 (s : N.State) (i : N.Inputs) :
  R.v39303 (state s) (inputs i) = Zmod.unsigned (N.v39303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39303 s i)) at 1.
  unfold R.v39303, N.v39303.
  rewrite ?node_39298.
  rewrite ?node_39302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39304 (s : N.State) (i : N.Inputs) :
  R.v39304 (state s) (inputs i) = Zmod.unsigned (N.v39304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39304 s i)) at 1.
  unfold R.v39304, N.v39304.
  unfold R.v6, N.v6.
  rewrite ?node_39303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39305 (s : N.State) (i : N.Inputs) :
  R.v39305 (state s) (inputs i) = Zmod.unsigned (N.v39305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39305 s i)) at 1.
  unfold R.v39305, N.v39305.
  rewrite ?node_6742.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39306 (s : N.State) (i : N.Inputs) :
  R.v39306 (state s) (inputs i) = Zmod.unsigned (N.v39306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39306 s i)) at 1.
  unfold R.v39306, N.v39306.
  unfold R.v6, N.v6.
  rewrite ?node_6852.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39307 (s : N.State) (i : N.Inputs) :
  R.v39307 (state s) (inputs i) = Zmod.unsigned (N.v39307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39307 s i)) at 1.
  unfold R.v39307, N.v39307.
  rewrite ?node_39305.
  rewrite ?node_39306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39308 (s : N.State) (i : N.Inputs) :
  R.v39308 (state s) (inputs i) = Zmod.unsigned (N.v39308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39308 s i)) at 1.
  unfold R.v39308, N.v39308.
  rewrite ?node_39304.
  rewrite ?node_39307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39309 (s : N.State) (i : N.Inputs) :
  R.v39309 (state s) (inputs i) = Zmod.unsigned (N.v39309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39309 s i)) at 1.
  unfold R.v39309, N.v39309.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39310 (s : N.State) (i : N.Inputs) :
  R.v39310 (state s) (inputs i) = Zmod.unsigned (N.v39310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39310 s i)) at 1.
  unfold R.v39310, N.v39310.
  unfold R.v6, N.v6.
  rewrite ?node_6749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39311 (s : N.State) (i : N.Inputs) :
  R.v39311 (state s) (inputs i) = Zmod.unsigned (N.v39311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39311 s i)) at 1.
  unfold R.v39311, N.v39311.
  unfold R.v6, N.v6.
  rewrite ?node_6746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39312 (s : N.State) (i : N.Inputs) :
  R.v39312 (state s) (inputs i) = Zmod.unsigned (N.v39312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39312 s i)) at 1.
  unfold R.v39312, N.v39312.
  rewrite ?node_39310.
  rewrite ?node_39311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39313 (s : N.State) (i : N.Inputs) :
  R.v39313 (state s) (inputs i) = Zmod.unsigned (N.v39313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39313 s i)) at 1.
  unfold R.v39313, N.v39313.
  unfold R.v16463, N.v16463.
  rewrite ?node_39312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39314 (s : N.State) (i : N.Inputs) :
  R.v39314 (state s) (inputs i) = Zmod.unsigned (N.v39314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39314 s i)) at 1.
  unfold R.v39314, N.v39314.
  rewrite ?node_6750.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39315 (s : N.State) (i : N.Inputs) :
  R.v39315 (state s) (inputs i) = Zmod.unsigned (N.v39315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39315 s i)) at 1.
  unfold R.v39315, N.v39315.
  unfold R.v6, N.v6.
  rewrite ?node_6853.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39316 (s : N.State) (i : N.Inputs) :
  R.v39316 (state s) (inputs i) = Zmod.unsigned (N.v39316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39316 s i)) at 1.
  unfold R.v39316, N.v39316.
  rewrite ?node_39314.
  rewrite ?node_39315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39317 (s : N.State) (i : N.Inputs) :
  R.v39317 (state s) (inputs i) = Zmod.unsigned (N.v39317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39317 s i)) at 1.
  unfold R.v39317, N.v39317.
  rewrite ?node_39313.
  rewrite ?node_39316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39318 (s : N.State) (i : N.Inputs) :
  R.v39318 (state s) (inputs i) = Zmod.unsigned (N.v39318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39318 s i)) at 1.
  unfold R.v39318, N.v39318.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39319 (s : N.State) (i : N.Inputs) :
  R.v39319 (state s) (inputs i) = Zmod.unsigned (N.v39319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39319 s i)) at 1.
  unfold R.v39319, N.v39319.
  rewrite ?node_6812.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39320 (s : N.State) (i : N.Inputs) :
  R.v39320 (state s) (inputs i) = Zmod.unsigned (N.v39320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39320 s i)) at 1.
  unfold R.v39320, N.v39320.
  rewrite ?node_6808.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39321 (s : N.State) (i : N.Inputs) :
  R.v39321 (state s) (inputs i) = Zmod.unsigned (N.v39321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39321 s i)) at 1.
  unfold R.v39321, N.v39321.
  rewrite ?node_6800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39322 (s : N.State) (i : N.Inputs) :
  R.v39322 (state s) (inputs i) = Zmod.unsigned (N.v39322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39322 s i)) at 1.
  unfold R.v39322, N.v39322.
  unfold R.v6, N.v6.
  rewrite ?node_6792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39323 (s : N.State) (i : N.Inputs) :
  R.v39323 (state s) (inputs i) = Zmod.unsigned (N.v39323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39323 s i)) at 1.
  unfold R.v39323, N.v39323.
  unfold R.v6, N.v6.
  rewrite ?node_6785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39324 (s : N.State) (i : N.Inputs) :
  R.v39324 (state s) (inputs i) = Zmod.unsigned (N.v39324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39324 s i)) at 1.
  unfold R.v39324, N.v39324.
  rewrite ?node_39322.
  rewrite ?node_39323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39325 (s : N.State) (i : N.Inputs) :
  R.v39325 (state s) (inputs i) = Zmod.unsigned (N.v39325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39325 s i)) at 1.
  unfold R.v39325, N.v39325.
  unfold R.v16484, N.v16484.
  rewrite ?node_39324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39326 (s : N.State) (i : N.Inputs) :
  R.v39326 (state s) (inputs i) = Zmod.unsigned (N.v39326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39326 s i)) at 1.
  unfold R.v39326, N.v39326.
  rewrite ?node_39319.
  rewrite ?node_39320.
  rewrite ?node_39321.
  rewrite ?node_39325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39327 (s : N.State) (i : N.Inputs) :
  R.v39327 (state s) (inputs i) = Zmod.unsigned (N.v39327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39327 s i)) at 1.
  unfold R.v39327, N.v39327.
  unfold R.v6, N.v6.
  rewrite ?node_39326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39328 (s : N.State) (i : N.Inputs) :
  R.v39328 (state s) (inputs i) = Zmod.unsigned (N.v39328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39328 s i)) at 1.
  unfold R.v39328, N.v39328.
  rewrite ?node_6813.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39329 (s : N.State) (i : N.Inputs) :
  R.v39329 (state s) (inputs i) = Zmod.unsigned (N.v39329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39329 s i)) at 1.
  unfold R.v39329, N.v39329.
  unfold R.v6, N.v6.
  rewrite ?node_6904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39330 (s : N.State) (i : N.Inputs) :
  R.v39330 (state s) (inputs i) = Zmod.unsigned (N.v39330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39330 s i)) at 1.
  unfold R.v39330, N.v39330.
  unfold R.v6, N.v6.
  rewrite ?node_6938.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39331 (s : N.State) (i : N.Inputs) :
  R.v39331 (state s) (inputs i) = Zmod.unsigned (N.v39331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39331 s i)) at 1.
  unfold R.v39331, N.v39331.
  rewrite ?node_39328.
  rewrite ?node_39329.
  rewrite ?node_39330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39332 (s : N.State) (i : N.Inputs) :
  R.v39332 (state s) (inputs i) = Zmod.unsigned (N.v39332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39332 s i)) at 1.
  unfold R.v39332, N.v39332.
  rewrite ?node_39327.
  rewrite ?node_39331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39333 (s : N.State) (i : N.Inputs) :
  R.v39333 (state s) (inputs i) = Zmod.unsigned (N.v39333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39333 s i)) at 1.
  unfold R.v39333, N.v39333.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39334 (s : N.State) (i : N.Inputs) :
  R.v39334 (state s) (inputs i) = Zmod.unsigned (N.v39334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39334 s i)) at 1.
  unfold R.v39334, N.v39334.
  rewrite ?node_6800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39335 (s : N.State) (i : N.Inputs) :
  R.v39335 (state s) (inputs i) = Zmod.unsigned (N.v39335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39335 s i)) at 1.
  unfold R.v39335, N.v39335.
  unfold R.v6, N.v6.
  rewrite ?node_6792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39336 (s : N.State) (i : N.Inputs) :
  R.v39336 (state s) (inputs i) = Zmod.unsigned (N.v39336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39336 s i)) at 1.
  unfold R.v39336, N.v39336.
  unfold R.v6, N.v6.
  rewrite ?node_6785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39337 (s : N.State) (i : N.Inputs) :
  R.v39337 (state s) (inputs i) = Zmod.unsigned (N.v39337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39337 s i)) at 1.
  unfold R.v39337, N.v39337.
  rewrite ?node_39335.
  rewrite ?node_39336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39338 (s : N.State) (i : N.Inputs) :
  R.v39338 (state s) (inputs i) = Zmod.unsigned (N.v39338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39338 s i)) at 1.
  unfold R.v39338, N.v39338.
  unfold R.v16484, N.v16484.
  rewrite ?node_39337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39339 (s : N.State) (i : N.Inputs) :
  R.v39339 (state s) (inputs i) = Zmod.unsigned (N.v39339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39339 s i)) at 1.
  unfold R.v39339, N.v39339.
  rewrite ?node_39334.
  rewrite ?node_39338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39340 (s : N.State) (i : N.Inputs) :
  R.v39340 (state s) (inputs i) = Zmod.unsigned (N.v39340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39340 s i)) at 1.
  unfold R.v39340, N.v39340.
  unfold R.v6, N.v6.
  rewrite ?node_39339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39341 (s : N.State) (i : N.Inputs) :
  R.v39341 (state s) (inputs i) = Zmod.unsigned (N.v39341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39341 s i)) at 1.
  unfold R.v39341, N.v39341.
  rewrite ?node_6801.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39342 (s : N.State) (i : N.Inputs) :
  R.v39342 (state s) (inputs i) = Zmod.unsigned (N.v39342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39342 s i)) at 1.
  unfold R.v39342, N.v39342.
  unfold R.v6, N.v6.
  rewrite ?node_6904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39343 (s : N.State) (i : N.Inputs) :
  R.v39343 (state s) (inputs i) = Zmod.unsigned (N.v39343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39343 s i)) at 1.
  unfold R.v39343, N.v39343.
  rewrite ?node_39341.
  rewrite ?node_39342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39344 (s : N.State) (i : N.Inputs) :
  R.v39344 (state s) (inputs i) = Zmod.unsigned (N.v39344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39344 s i)) at 1.
  unfold R.v39344, N.v39344.
  rewrite ?node_39340.
  rewrite ?node_39343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39345 (s : N.State) (i : N.Inputs) :
  R.v39345 (state s) (inputs i) = Zmod.unsigned (N.v39345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39345 s i)) at 1.
  unfold R.v39345, N.v39345.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39346 (s : N.State) (i : N.Inputs) :
  R.v39346 (state s) (inputs i) = Zmod.unsigned (N.v39346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39346 s i)) at 1.
  unfold R.v39346, N.v39346.
  rewrite ?node_6812.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39347 (s : N.State) (i : N.Inputs) :
  R.v39347 (state s) (inputs i) = Zmod.unsigned (N.v39347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39347 s i)) at 1.
  unfold R.v39347, N.v39347.
  unfold R.v6, N.v6.
  rewrite ?node_6808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39348 (s : N.State) (i : N.Inputs) :
  R.v39348 (state s) (inputs i) = Zmod.unsigned (N.v39348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39348 s i)) at 1.
  unfold R.v39348, N.v39348.
  unfold R.v6, N.v6.
  rewrite ?node_6801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39349 (s : N.State) (i : N.Inputs) :
  R.v39349 (state s) (inputs i) = Zmod.unsigned (N.v39349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39349 s i)) at 1.
  unfold R.v39349, N.v39349.
  rewrite ?node_39347.
  rewrite ?node_39348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39350 (s : N.State) (i : N.Inputs) :
  R.v39350 (state s) (inputs i) = Zmod.unsigned (N.v39350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39350 s i)) at 1.
  unfold R.v39350, N.v39350.
  unfold R.v16484, N.v16484.
  rewrite ?node_39349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39351 (s : N.State) (i : N.Inputs) :
  R.v39351 (state s) (inputs i) = Zmod.unsigned (N.v39351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39351 s i)) at 1.
  unfold R.v39351, N.v39351.
  rewrite ?node_39346.
  rewrite ?node_39350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39352 (s : N.State) (i : N.Inputs) :
  R.v39352 (state s) (inputs i) = Zmod.unsigned (N.v39352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39352 s i)) at 1.
  unfold R.v39352, N.v39352.
  unfold R.v6, N.v6.
  rewrite ?node_39351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39353 (s : N.State) (i : N.Inputs) :
  R.v39353 (state s) (inputs i) = Zmod.unsigned (N.v39353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39353 s i)) at 1.
  unfold R.v39353, N.v39353.
  rewrite ?node_6813.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39354 (s : N.State) (i : N.Inputs) :
  R.v39354 (state s) (inputs i) = Zmod.unsigned (N.v39354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39354 s i)) at 1.
  unfold R.v39354, N.v39354.
  unfold R.v6, N.v6.
  rewrite ?node_6938.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39355 (s : N.State) (i : N.Inputs) :
  R.v39355 (state s) (inputs i) = Zmod.unsigned (N.v39355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39355 s i)) at 1.
  unfold R.v39355, N.v39355.
  rewrite ?node_39353.
  rewrite ?node_39354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39356 (s : N.State) (i : N.Inputs) :
  R.v39356 (state s) (inputs i) = Zmod.unsigned (N.v39356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39356 s i)) at 1.
  unfold R.v39356, N.v39356.
  rewrite ?node_39352.
  rewrite ?node_39355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39357 (s : N.State) (i : N.Inputs) :
  R.v39357 (state s) (inputs i) = Zmod.unsigned (N.v39357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39357 s i)) at 1.
  unfold R.v39357, N.v39357.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39358 (s : N.State) (i : N.Inputs) :
  R.v39358 (state s) (inputs i) = Zmod.unsigned (N.v39358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39358 s i)) at 1.
  unfold R.v39358, N.v39358.
  rewrite ?node_6831.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39359 (s : N.State) (i : N.Inputs) :
  R.v39359 (state s) (inputs i) = Zmod.unsigned (N.v39359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39359 s i)) at 1.
  unfold R.v39359, N.v39359.
  rewrite ?node_6827.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39360 (s : N.State) (i : N.Inputs) :
  R.v39360 (state s) (inputs i) = Zmod.unsigned (N.v39360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39360 s i)) at 1.
  unfold R.v39360, N.v39360.
  rewrite ?node_6823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39361 (s : N.State) (i : N.Inputs) :
  R.v39361 (state s) (inputs i) = Zmod.unsigned (N.v39361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39361 s i)) at 1.
  unfold R.v39361, N.v39361.
  unfold R.v6, N.v6.
  rewrite ?node_6819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39362 (s : N.State) (i : N.Inputs) :
  R.v39362 (state s) (inputs i) = Zmod.unsigned (N.v39362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39362 s i)) at 1.
  unfold R.v39362, N.v39362.
  unfold R.v6, N.v6.
  rewrite ?node_6816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39363 (s : N.State) (i : N.Inputs) :
  R.v39363 (state s) (inputs i) = Zmod.unsigned (N.v39363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39363 s i)) at 1.
  unfold R.v39363, N.v39363.
  rewrite ?node_39361.
  rewrite ?node_39362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39364 (s : N.State) (i : N.Inputs) :
  R.v39364 (state s) (inputs i) = Zmod.unsigned (N.v39364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39364 s i)) at 1.
  unfold R.v39364, N.v39364.
  unfold R.v16484, N.v16484.
  rewrite ?node_39363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39365 (s : N.State) (i : N.Inputs) :
  R.v39365 (state s) (inputs i) = Zmod.unsigned (N.v39365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39365 s i)) at 1.
  unfold R.v39365, N.v39365.
  rewrite ?node_39358.
  rewrite ?node_39359.
  rewrite ?node_39360.
  rewrite ?node_39364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39366 (s : N.State) (i : N.Inputs) :
  R.v39366 (state s) (inputs i) = Zmod.unsigned (N.v39366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39366 s i)) at 1.
  unfold R.v39366, N.v39366.
  unfold R.v6, N.v6.
  rewrite ?node_39365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39367 (s : N.State) (i : N.Inputs) :
  R.v39367 (state s) (inputs i) = Zmod.unsigned (N.v39367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39367 s i)) at 1.
  unfold R.v39367, N.v39367.
  rewrite ?node_6832.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39368 (s : N.State) (i : N.Inputs) :
  R.v39368 (state s) (inputs i) = Zmod.unsigned (N.v39368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39368 s i)) at 1.
  unfold R.v39368, N.v39368.
  unfold R.v6, N.v6.
  rewrite ?node_6927.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39369 (s : N.State) (i : N.Inputs) :
  R.v39369 (state s) (inputs i) = Zmod.unsigned (N.v39369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39369 s i)) at 1.
  unfold R.v39369, N.v39369.
  unfold R.v6, N.v6.
  rewrite ?node_6946.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39370 (s : N.State) (i : N.Inputs) :
  R.v39370 (state s) (inputs i) = Zmod.unsigned (N.v39370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39370 s i)) at 1.
  unfold R.v39370, N.v39370.
  rewrite ?node_39367.
  rewrite ?node_39368.
  rewrite ?node_39369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39371 (s : N.State) (i : N.Inputs) :
  R.v39371 (state s) (inputs i) = Zmod.unsigned (N.v39371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39371 s i)) at 1.
  unfold R.v39371, N.v39371.
  rewrite ?node_39366.
  rewrite ?node_39370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39372 (s : N.State) (i : N.Inputs) :
  R.v39372 (state s) (inputs i) = Zmod.unsigned (N.v39372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39372 s i)) at 1.
  unfold R.v39372, N.v39372.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39373 (s : N.State) (i : N.Inputs) :
  R.v39373 (state s) (inputs i) = Zmod.unsigned (N.v39373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39373 s i)) at 1.
  unfold R.v39373, N.v39373.
  rewrite ?node_6823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39374 (s : N.State) (i : N.Inputs) :
  R.v39374 (state s) (inputs i) = Zmod.unsigned (N.v39374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39374 s i)) at 1.
  unfold R.v39374, N.v39374.
  unfold R.v6, N.v6.
  rewrite ?node_6819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39375 (s : N.State) (i : N.Inputs) :
  R.v39375 (state s) (inputs i) = Zmod.unsigned (N.v39375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39375 s i)) at 1.
  unfold R.v39375, N.v39375.
  unfold R.v6, N.v6.
  rewrite ?node_6816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39376 (s : N.State) (i : N.Inputs) :
  R.v39376 (state s) (inputs i) = Zmod.unsigned (N.v39376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39376 s i)) at 1.
  unfold R.v39376, N.v39376.
  rewrite ?node_39374.
  rewrite ?node_39375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39377 (s : N.State) (i : N.Inputs) :
  R.v39377 (state s) (inputs i) = Zmod.unsigned (N.v39377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39377 s i)) at 1.
  unfold R.v39377, N.v39377.
  unfold R.v16484, N.v16484.
  rewrite ?node_39376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39378 (s : N.State) (i : N.Inputs) :
  R.v39378 (state s) (inputs i) = Zmod.unsigned (N.v39378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39378 s i)) at 1.
  unfold R.v39378, N.v39378.
  rewrite ?node_39373.
  rewrite ?node_39377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39379 (s : N.State) (i : N.Inputs) :
  R.v39379 (state s) (inputs i) = Zmod.unsigned (N.v39379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39379 s i)) at 1.
  unfold R.v39379, N.v39379.
  unfold R.v6, N.v6.
  rewrite ?node_39378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39380 (s : N.State) (i : N.Inputs) :
  R.v39380 (state s) (inputs i) = Zmod.unsigned (N.v39380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39380 s i)) at 1.
  unfold R.v39380, N.v39380.
  rewrite ?node_6824.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39381 (s : N.State) (i : N.Inputs) :
  R.v39381 (state s) (inputs i) = Zmod.unsigned (N.v39381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39381 s i)) at 1.
  unfold R.v39381, N.v39381.
  unfold R.v6, N.v6.
  rewrite ?node_6927.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39382 (s : N.State) (i : N.Inputs) :
  R.v39382 (state s) (inputs i) = Zmod.unsigned (N.v39382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39382 s i)) at 1.
  unfold R.v39382, N.v39382.
  rewrite ?node_39380.
  rewrite ?node_39381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39383 (s : N.State) (i : N.Inputs) :
  R.v39383 (state s) (inputs i) = Zmod.unsigned (N.v39383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39383 s i)) at 1.
  unfold R.v39383, N.v39383.
  rewrite ?node_39379.
  rewrite ?node_39382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39384 (s : N.State) (i : N.Inputs) :
  R.v39384 (state s) (inputs i) = Zmod.unsigned (N.v39384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39384 s i)) at 1.
  unfold R.v39384, N.v39384.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39385 (s : N.State) (i : N.Inputs) :
  R.v39385 (state s) (inputs i) = Zmod.unsigned (N.v39385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39385 s i)) at 1.
  unfold R.v39385, N.v39385.
  rewrite ?node_6831.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39386 (s : N.State) (i : N.Inputs) :
  R.v39386 (state s) (inputs i) = Zmod.unsigned (N.v39386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39386 s i)) at 1.
  unfold R.v39386, N.v39386.
  unfold R.v6, N.v6.
  rewrite ?node_6827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39387 (s : N.State) (i : N.Inputs) :
  R.v39387 (state s) (inputs i) = Zmod.unsigned (N.v39387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39387 s i)) at 1.
  unfold R.v39387, N.v39387.
  unfold R.v6, N.v6.
  rewrite ?node_6824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39388 (s : N.State) (i : N.Inputs) :
  R.v39388 (state s) (inputs i) = Zmod.unsigned (N.v39388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39388 s i)) at 1.
  unfold R.v39388, N.v39388.
  rewrite ?node_39386.
  rewrite ?node_39387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39389 (s : N.State) (i : N.Inputs) :
  R.v39389 (state s) (inputs i) = Zmod.unsigned (N.v39389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39389 s i)) at 1.
  unfold R.v39389, N.v39389.
  unfold R.v16484, N.v16484.
  rewrite ?node_39388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39390 (s : N.State) (i : N.Inputs) :
  R.v39390 (state s) (inputs i) = Zmod.unsigned (N.v39390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39390 s i)) at 1.
  unfold R.v39390, N.v39390.
  rewrite ?node_39385.
  rewrite ?node_39389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39391 (s : N.State) (i : N.Inputs) :
  R.v39391 (state s) (inputs i) = Zmod.unsigned (N.v39391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39391 s i)) at 1.
  unfold R.v39391, N.v39391.
  unfold R.v6, N.v6.
  rewrite ?node_39390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39392 (s : N.State) (i : N.Inputs) :
  R.v39392 (state s) (inputs i) = Zmod.unsigned (N.v39392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39392 s i)) at 1.
  unfold R.v39392, N.v39392.
  rewrite ?node_6832.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39393 (s : N.State) (i : N.Inputs) :
  R.v39393 (state s) (inputs i) = Zmod.unsigned (N.v39393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39393 s i)) at 1.
  unfold R.v39393, N.v39393.
  unfold R.v6, N.v6.
  rewrite ?node_6946.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39394 (s : N.State) (i : N.Inputs) :
  R.v39394 (state s) (inputs i) = Zmod.unsigned (N.v39394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39394 s i)) at 1.
  unfold R.v39394, N.v39394.
  rewrite ?node_39392.
  rewrite ?node_39393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39395 (s : N.State) (i : N.Inputs) :
  R.v39395 (state s) (inputs i) = Zmod.unsigned (N.v39395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39395 s i)) at 1.
  unfold R.v39395, N.v39395.
  rewrite ?node_39391.
  rewrite ?node_39394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39396 (s : N.State) (i : N.Inputs) :
  R.v39396 (state s) (inputs i) = Zmod.unsigned (N.v39396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39396 s i)) at 1.
  unfold R.v39396, N.v39396.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39397 (s : N.State) (i : N.Inputs) :
  R.v39397 (state s) (inputs i) = Zmod.unsigned (N.v39397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39397 s i)) at 1.
  unfold R.v39397, N.v39397.
  unfold R.v6, N.v6.
  rewrite ?node_6839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39398 (s : N.State) (i : N.Inputs) :
  R.v39398 (state s) (inputs i) = Zmod.unsigned (N.v39398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39398 s i)) at 1.
  unfold R.v39398, N.v39398.
  unfold R.v6, N.v6.
  rewrite ?node_6836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39399 (s : N.State) (i : N.Inputs) :
  R.v39399 (state s) (inputs i) = Zmod.unsigned (N.v39399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39399 s i)) at 1.
  unfold R.v39399, N.v39399.
  rewrite ?node_39397.
  rewrite ?node_39398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39400 (s : N.State) (i : N.Inputs) :
  R.v39400 (state s) (inputs i) = Zmod.unsigned (N.v39400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39400 s i)) at 1.
  unfold R.v39400, N.v39400.
  unfold R.v16463, N.v16463.
  rewrite ?node_39399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39401 (s : N.State) (i : N.Inputs) :
  R.v39401 (state s) (inputs i) = Zmod.unsigned (N.v39401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39401 s i)) at 1.
  unfold R.v39401, N.v39401.
  rewrite ?node_6840.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39402 (s : N.State) (i : N.Inputs) :
  R.v39402 (state s) (inputs i) = Zmod.unsigned (N.v39402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39402 s i)) at 1.
  unfold R.v39402, N.v39402.
  unfold R.v6, N.v6.
  rewrite ?node_6947.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39403 (s : N.State) (i : N.Inputs) :
  R.v39403 (state s) (inputs i) = Zmod.unsigned (N.v39403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39403 s i)) at 1.
  unfold R.v39403, N.v39403.
  rewrite ?node_39401.
  rewrite ?node_39402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39404 (s : N.State) (i : N.Inputs) :
  R.v39404 (state s) (inputs i) = Zmod.unsigned (N.v39404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39404 s i)) at 1.
  unfold R.v39404, N.v39404.
  rewrite ?node_39400.
  rewrite ?node_39403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39405 (s : N.State) (i : N.Inputs) :
  R.v39405 (state s) (inputs i) = Zmod.unsigned (N.v39405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39405 s i)) at 1.
  unfold R.v39405, N.v39405.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39406 (s : N.State) (i : N.Inputs) :
  R.v39406 (state s) (inputs i) = Zmod.unsigned (N.v39406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39406 s i)) at 1.
  unfold R.v39406, N.v39406.
  rewrite ?node_6904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39407 (s : N.State) (i : N.Inputs) :
  R.v39407 (state s) (inputs i) = Zmod.unsigned (N.v39407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39407 s i)) at 1.
  unfold R.v39407, N.v39407.
  rewrite ?node_6900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39408 (s : N.State) (i : N.Inputs) :
  R.v39408 (state s) (inputs i) = Zmod.unsigned (N.v39408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39408 s i)) at 1.
  unfold R.v39408, N.v39408.
  rewrite ?node_6892.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39409 (s : N.State) (i : N.Inputs) :
  R.v39409 (state s) (inputs i) = Zmod.unsigned (N.v39409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39409 s i)) at 1.
  unfold R.v39409, N.v39409.
  unfold R.v6, N.v6.
  rewrite ?node_6884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39410 (s : N.State) (i : N.Inputs) :
  R.v39410 (state s) (inputs i) = Zmod.unsigned (N.v39410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39410 s i)) at 1.
  unfold R.v39410, N.v39410.
  unfold R.v6, N.v6.
  rewrite ?node_6877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39411 (s : N.State) (i : N.Inputs) :
  R.v39411 (state s) (inputs i) = Zmod.unsigned (N.v39411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39411 s i)) at 1.
  unfold R.v39411, N.v39411.
  rewrite ?node_39409.
  rewrite ?node_39410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39412 (s : N.State) (i : N.Inputs) :
  R.v39412 (state s) (inputs i) = Zmod.unsigned (N.v39412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39412 s i)) at 1.
  unfold R.v39412, N.v39412.
  unfold R.v16484, N.v16484.
  rewrite ?node_39411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39413 (s : N.State) (i : N.Inputs) :
  R.v39413 (state s) (inputs i) = Zmod.unsigned (N.v39413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39413 s i)) at 1.
  unfold R.v39413, N.v39413.
  rewrite ?node_39406.
  rewrite ?node_39407.
  rewrite ?node_39408.
  rewrite ?node_39412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39414 (s : N.State) (i : N.Inputs) :
  R.v39414 (state s) (inputs i) = Zmod.unsigned (N.v39414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39414 s i)) at 1.
  unfold R.v39414, N.v39414.
  unfold R.v6, N.v6.
  rewrite ?node_39413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39415 (s : N.State) (i : N.Inputs) :
  R.v39415 (state s) (inputs i) = Zmod.unsigned (N.v39415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39415 s i)) at 1.
  unfold R.v39415, N.v39415.
  rewrite ?node_6905.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39416 (s : N.State) (i : N.Inputs) :
  R.v39416 (state s) (inputs i) = Zmod.unsigned (N.v39416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39416 s i)) at 1.
  unfold R.v39416, N.v39416.
  unfold R.v6, N.v6.
  rewrite ?node_7000.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39417 (s : N.State) (i : N.Inputs) :
  R.v39417 (state s) (inputs i) = Zmod.unsigned (N.v39417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39417 s i)) at 1.
  unfold R.v39417, N.v39417.
  unfold R.v6, N.v6.
  rewrite ?node_7037.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39418 (s : N.State) (i : N.Inputs) :
  R.v39418 (state s) (inputs i) = Zmod.unsigned (N.v39418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39418 s i)) at 1.
  unfold R.v39418, N.v39418.
  rewrite ?node_39415.
  rewrite ?node_39416.
  rewrite ?node_39417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39419 (s : N.State) (i : N.Inputs) :
  R.v39419 (state s) (inputs i) = Zmod.unsigned (N.v39419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39419 s i)) at 1.
  unfold R.v39419, N.v39419.
  rewrite ?node_39414.
  rewrite ?node_39418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39420 (s : N.State) (i : N.Inputs) :
  R.v39420 (state s) (inputs i) = Zmod.unsigned (N.v39420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39420 s i)) at 1.
  unfold R.v39420, N.v39420.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39421 (s : N.State) (i : N.Inputs) :
  R.v39421 (state s) (inputs i) = Zmod.unsigned (N.v39421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39421 s i)) at 1.
  unfold R.v39421, N.v39421.
  rewrite ?node_6892.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39422 (s : N.State) (i : N.Inputs) :
  R.v39422 (state s) (inputs i) = Zmod.unsigned (N.v39422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39422 s i)) at 1.
  unfold R.v39422, N.v39422.
  unfold R.v6, N.v6.
  rewrite ?node_6884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39423 (s : N.State) (i : N.Inputs) :
  R.v39423 (state s) (inputs i) = Zmod.unsigned (N.v39423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39423 s i)) at 1.
  unfold R.v39423, N.v39423.
  unfold R.v6, N.v6.
  rewrite ?node_6877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39424 (s : N.State) (i : N.Inputs) :
  R.v39424 (state s) (inputs i) = Zmod.unsigned (N.v39424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39424 s i)) at 1.
  unfold R.v39424, N.v39424.
  rewrite ?node_39422.
  rewrite ?node_39423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39425 (s : N.State) (i : N.Inputs) :
  R.v39425 (state s) (inputs i) = Zmod.unsigned (N.v39425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39425 s i)) at 1.
  unfold R.v39425, N.v39425.
  unfold R.v16484, N.v16484.
  rewrite ?node_39424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39426 (s : N.State) (i : N.Inputs) :
  R.v39426 (state s) (inputs i) = Zmod.unsigned (N.v39426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39426 s i)) at 1.
  unfold R.v39426, N.v39426.
  rewrite ?node_39421.
  rewrite ?node_39425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39427 (s : N.State) (i : N.Inputs) :
  R.v39427 (state s) (inputs i) = Zmod.unsigned (N.v39427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39427 s i)) at 1.
  unfold R.v39427, N.v39427.
  unfold R.v6, N.v6.
  rewrite ?node_39426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39428 (s : N.State) (i : N.Inputs) :
  R.v39428 (state s) (inputs i) = Zmod.unsigned (N.v39428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39428 s i)) at 1.
  unfold R.v39428, N.v39428.
  rewrite ?node_6893.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39429 (s : N.State) (i : N.Inputs) :
  R.v39429 (state s) (inputs i) = Zmod.unsigned (N.v39429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39429 s i)) at 1.
  unfold R.v39429, N.v39429.
  unfold R.v6, N.v6.
  rewrite ?node_7000.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39430 (s : N.State) (i : N.Inputs) :
  R.v39430 (state s) (inputs i) = Zmod.unsigned (N.v39430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39430 s i)) at 1.
  unfold R.v39430, N.v39430.
  rewrite ?node_39428.
  rewrite ?node_39429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39431 (s : N.State) (i : N.Inputs) :
  R.v39431 (state s) (inputs i) = Zmod.unsigned (N.v39431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39431 s i)) at 1.
  unfold R.v39431, N.v39431.
  rewrite ?node_39427.
  rewrite ?node_39430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39432 (s : N.State) (i : N.Inputs) :
  R.v39432 (state s) (inputs i) = Zmod.unsigned (N.v39432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39432 s i)) at 1.
  unfold R.v39432, N.v39432.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39433 (s : N.State) (i : N.Inputs) :
  R.v39433 (state s) (inputs i) = Zmod.unsigned (N.v39433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39433 s i)) at 1.
  unfold R.v39433, N.v39433.
  rewrite ?node_6904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39434 (s : N.State) (i : N.Inputs) :
  R.v39434 (state s) (inputs i) = Zmod.unsigned (N.v39434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39434 s i)) at 1.
  unfold R.v39434, N.v39434.
  unfold R.v6, N.v6.
  rewrite ?node_6900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39435 (s : N.State) (i : N.Inputs) :
  R.v39435 (state s) (inputs i) = Zmod.unsigned (N.v39435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39435 s i)) at 1.
  unfold R.v39435, N.v39435.
  unfold R.v6, N.v6.
  rewrite ?node_6893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39436 (s : N.State) (i : N.Inputs) :
  R.v39436 (state s) (inputs i) = Zmod.unsigned (N.v39436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39436 s i)) at 1.
  unfold R.v39436, N.v39436.
  rewrite ?node_39434.
  rewrite ?node_39435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39437 (s : N.State) (i : N.Inputs) :
  R.v39437 (state s) (inputs i) = Zmod.unsigned (N.v39437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39437 s i)) at 1.
  unfold R.v39437, N.v39437.
  unfold R.v16484, N.v16484.
  rewrite ?node_39436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39438 (s : N.State) (i : N.Inputs) :
  R.v39438 (state s) (inputs i) = Zmod.unsigned (N.v39438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39438 s i)) at 1.
  unfold R.v39438, N.v39438.
  rewrite ?node_39433.
  rewrite ?node_39437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39439 (s : N.State) (i : N.Inputs) :
  R.v39439 (state s) (inputs i) = Zmod.unsigned (N.v39439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39439 s i)) at 1.
  unfold R.v39439, N.v39439.
  unfold R.v6, N.v6.
  rewrite ?node_39438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39440 (s : N.State) (i : N.Inputs) :
  R.v39440 (state s) (inputs i) = Zmod.unsigned (N.v39440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39440 s i)) at 1.
  unfold R.v39440, N.v39440.
  rewrite ?node_6905.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39441 (s : N.State) (i : N.Inputs) :
  R.v39441 (state s) (inputs i) = Zmod.unsigned (N.v39441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39441 s i)) at 1.
  unfold R.v39441, N.v39441.
  unfold R.v6, N.v6.
  rewrite ?node_7037.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39442 (s : N.State) (i : N.Inputs) :
  R.v39442 (state s) (inputs i) = Zmod.unsigned (N.v39442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39442 s i)) at 1.
  unfold R.v39442, N.v39442.
  rewrite ?node_39440.
  rewrite ?node_39441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39443 (s : N.State) (i : N.Inputs) :
  R.v39443 (state s) (inputs i) = Zmod.unsigned (N.v39443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39443 s i)) at 1.
  unfold R.v39443, N.v39443.
  rewrite ?node_39439.
  rewrite ?node_39442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39444 (s : N.State) (i : N.Inputs) :
  R.v39444 (state s) (inputs i) = Zmod.unsigned (N.v39444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39444 s i)) at 1.
  unfold R.v39444, N.v39444.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39445 (s : N.State) (i : N.Inputs) :
  R.v39445 (state s) (inputs i) = Zmod.unsigned (N.v39445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39445 s i)) at 1.
  unfold R.v39445, N.v39445.
  rewrite ?node_6927.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39446 (s : N.State) (i : N.Inputs) :
  R.v39446 (state s) (inputs i) = Zmod.unsigned (N.v39446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39446 s i)) at 1.
  unfold R.v39446, N.v39446.
  rewrite ?node_6923.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39447 (s : N.State) (i : N.Inputs) :
  R.v39447 (state s) (inputs i) = Zmod.unsigned (N.v39447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39447 s i)) at 1.
  unfold R.v39447, N.v39447.
  rewrite ?node_6919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39448 (s : N.State) (i : N.Inputs) :
  R.v39448 (state s) (inputs i) = Zmod.unsigned (N.v39448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39448 s i)) at 1.
  unfold R.v39448, N.v39448.
  unfold R.v6, N.v6.
  rewrite ?node_6915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39449 (s : N.State) (i : N.Inputs) :
  R.v39449 (state s) (inputs i) = Zmod.unsigned (N.v39449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39449 s i)) at 1.
  unfold R.v39449, N.v39449.
  unfold R.v6, N.v6.
  rewrite ?node_6912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39450 (s : N.State) (i : N.Inputs) :
  R.v39450 (state s) (inputs i) = Zmod.unsigned (N.v39450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39450 s i)) at 1.
  unfold R.v39450, N.v39450.
  rewrite ?node_39448.
  rewrite ?node_39449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39451 (s : N.State) (i : N.Inputs) :
  R.v39451 (state s) (inputs i) = Zmod.unsigned (N.v39451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39451 s i)) at 1.
  unfold R.v39451, N.v39451.
  unfold R.v16484, N.v16484.
  rewrite ?node_39450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39452 (s : N.State) (i : N.Inputs) :
  R.v39452 (state s) (inputs i) = Zmod.unsigned (N.v39452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39452 s i)) at 1.
  unfold R.v39452, N.v39452.
  rewrite ?node_39445.
  rewrite ?node_39446.
  rewrite ?node_39447.
  rewrite ?node_39451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39453 (s : N.State) (i : N.Inputs) :
  R.v39453 (state s) (inputs i) = Zmod.unsigned (N.v39453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39453 s i)) at 1.
  unfold R.v39453, N.v39453.
  unfold R.v6, N.v6.
  rewrite ?node_39452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39454 (s : N.State) (i : N.Inputs) :
  R.v39454 (state s) (inputs i) = Zmod.unsigned (N.v39454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39454 s i)) at 1.
  unfold R.v39454, N.v39454.
  rewrite ?node_6928.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39455 (s : N.State) (i : N.Inputs) :
  R.v39455 (state s) (inputs i) = Zmod.unsigned (N.v39455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39455 s i)) at 1.
  unfold R.v39455, N.v39455.
  unfold R.v6, N.v6.
  rewrite ?node_7020.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39456 (s : N.State) (i : N.Inputs) :
  R.v39456 (state s) (inputs i) = Zmod.unsigned (N.v39456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39456 s i)) at 1.
  unfold R.v39456, N.v39456.
  unfold R.v6, N.v6.
  rewrite ?node_7045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39457 (s : N.State) (i : N.Inputs) :
  R.v39457 (state s) (inputs i) = Zmod.unsigned (N.v39457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39457 s i)) at 1.
  unfold R.v39457, N.v39457.
  rewrite ?node_39454.
  rewrite ?node_39455.
  rewrite ?node_39456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39458 (s : N.State) (i : N.Inputs) :
  R.v39458 (state s) (inputs i) = Zmod.unsigned (N.v39458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39458 s i)) at 1.
  unfold R.v39458, N.v39458.
  rewrite ?node_39453.
  rewrite ?node_39457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39459 (s : N.State) (i : N.Inputs) :
  R.v39459 (state s) (inputs i) = Zmod.unsigned (N.v39459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39459 s i)) at 1.
  unfold R.v39459, N.v39459.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39460 (s : N.State) (i : N.Inputs) :
  R.v39460 (state s) (inputs i) = Zmod.unsigned (N.v39460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39460 s i)) at 1.
  unfold R.v39460, N.v39460.
  rewrite ?node_6919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39461 (s : N.State) (i : N.Inputs) :
  R.v39461 (state s) (inputs i) = Zmod.unsigned (N.v39461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39461 s i)) at 1.
  unfold R.v39461, N.v39461.
  unfold R.v6, N.v6.
  rewrite ?node_6915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39462 (s : N.State) (i : N.Inputs) :
  R.v39462 (state s) (inputs i) = Zmod.unsigned (N.v39462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39462 s i)) at 1.
  unfold R.v39462, N.v39462.
  unfold R.v6, N.v6.
  rewrite ?node_6912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39463 (s : N.State) (i : N.Inputs) :
  R.v39463 (state s) (inputs i) = Zmod.unsigned (N.v39463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39463 s i)) at 1.
  unfold R.v39463, N.v39463.
  rewrite ?node_39461.
  rewrite ?node_39462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39464 (s : N.State) (i : N.Inputs) :
  R.v39464 (state s) (inputs i) = Zmod.unsigned (N.v39464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39464 s i)) at 1.
  unfold R.v39464, N.v39464.
  unfold R.v16484, N.v16484.
  rewrite ?node_39463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39465 (s : N.State) (i : N.Inputs) :
  R.v39465 (state s) (inputs i) = Zmod.unsigned (N.v39465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39465 s i)) at 1.
  unfold R.v39465, N.v39465.
  rewrite ?node_39460.
  rewrite ?node_39464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39466 (s : N.State) (i : N.Inputs) :
  R.v39466 (state s) (inputs i) = Zmod.unsigned (N.v39466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39466 s i)) at 1.
  unfold R.v39466, N.v39466.
  unfold R.v6, N.v6.
  rewrite ?node_39465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39467 (s : N.State) (i : N.Inputs) :
  R.v39467 (state s) (inputs i) = Zmod.unsigned (N.v39467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39467 s i)) at 1.
  unfold R.v39467, N.v39467.
  rewrite ?node_6920.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39468 (s : N.State) (i : N.Inputs) :
  R.v39468 (state s) (inputs i) = Zmod.unsigned (N.v39468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39468 s i)) at 1.
  unfold R.v39468, N.v39468.
  unfold R.v6, N.v6.
  rewrite ?node_7020.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39469 (s : N.State) (i : N.Inputs) :
  R.v39469 (state s) (inputs i) = Zmod.unsigned (N.v39469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39469 s i)) at 1.
  unfold R.v39469, N.v39469.
  rewrite ?node_39467.
  rewrite ?node_39468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39470 (s : N.State) (i : N.Inputs) :
  R.v39470 (state s) (inputs i) = Zmod.unsigned (N.v39470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39470 s i)) at 1.
  unfold R.v39470, N.v39470.
  rewrite ?node_39466.
  rewrite ?node_39469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39471 (s : N.State) (i : N.Inputs) :
  R.v39471 (state s) (inputs i) = Zmod.unsigned (N.v39471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39471 s i)) at 1.
  unfold R.v39471, N.v39471.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39472 (s : N.State) (i : N.Inputs) :
  R.v39472 (state s) (inputs i) = Zmod.unsigned (N.v39472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39472 s i)) at 1.
  unfold R.v39472, N.v39472.
  rewrite ?node_6927.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39473 (s : N.State) (i : N.Inputs) :
  R.v39473 (state s) (inputs i) = Zmod.unsigned (N.v39473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39473 s i)) at 1.
  unfold R.v39473, N.v39473.
  unfold R.v6, N.v6.
  rewrite ?node_6923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39474 (s : N.State) (i : N.Inputs) :
  R.v39474 (state s) (inputs i) = Zmod.unsigned (N.v39474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39474 s i)) at 1.
  unfold R.v39474, N.v39474.
  unfold R.v6, N.v6.
  rewrite ?node_6920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39475 (s : N.State) (i : N.Inputs) :
  R.v39475 (state s) (inputs i) = Zmod.unsigned (N.v39475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39475 s i)) at 1.
  unfold R.v39475, N.v39475.
  rewrite ?node_39473.
  rewrite ?node_39474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39476 (s : N.State) (i : N.Inputs) :
  R.v39476 (state s) (inputs i) = Zmod.unsigned (N.v39476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39476 s i)) at 1.
  unfold R.v39476, N.v39476.
  unfold R.v16484, N.v16484.
  rewrite ?node_39475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39477 (s : N.State) (i : N.Inputs) :
  R.v39477 (state s) (inputs i) = Zmod.unsigned (N.v39477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39477 s i)) at 1.
  unfold R.v39477, N.v39477.
  rewrite ?node_39472.
  rewrite ?node_39476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39478 (s : N.State) (i : N.Inputs) :
  R.v39478 (state s) (inputs i) = Zmod.unsigned (N.v39478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39478 s i)) at 1.
  unfold R.v39478, N.v39478.
  unfold R.v6, N.v6.
  rewrite ?node_39477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39479 (s : N.State) (i : N.Inputs) :
  R.v39479 (state s) (inputs i) = Zmod.unsigned (N.v39479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39479 s i)) at 1.
  unfold R.v39479, N.v39479.
  rewrite ?node_6928.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39480 (s : N.State) (i : N.Inputs) :
  R.v39480 (state s) (inputs i) = Zmod.unsigned (N.v39480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39480 s i)) at 1.
  unfold R.v39480, N.v39480.
  unfold R.v6, N.v6.
  rewrite ?node_7045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39481 (s : N.State) (i : N.Inputs) :
  R.v39481 (state s) (inputs i) = Zmod.unsigned (N.v39481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39481 s i)) at 1.
  unfold R.v39481, N.v39481.
  rewrite ?node_39479.
  rewrite ?node_39480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39482 (s : N.State) (i : N.Inputs) :
  R.v39482 (state s) (inputs i) = Zmod.unsigned (N.v39482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39482 s i)) at 1.
  unfold R.v39482, N.v39482.
  rewrite ?node_39478.
  rewrite ?node_39481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39483 (s : N.State) (i : N.Inputs) :
  R.v39483 (state s) (inputs i) = Zmod.unsigned (N.v39483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39483 s i)) at 1.
  unfold R.v39483, N.v39483.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39484 (s : N.State) (i : N.Inputs) :
  R.v39484 (state s) (inputs i) = Zmod.unsigned (N.v39484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39484 s i)) at 1.
  unfold R.v39484, N.v39484.
  unfold R.v6, N.v6.
  rewrite ?node_6933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39485 (s : N.State) (i : N.Inputs) :
  R.v39485 (state s) (inputs i) = Zmod.unsigned (N.v39485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39485 s i)) at 1.
  unfold R.v39485, N.v39485.
  unfold R.v6, N.v6.
  rewrite ?node_6932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39486 (s : N.State) (i : N.Inputs) :
  R.v39486 (state s) (inputs i) = Zmod.unsigned (N.v39486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39486 s i)) at 1.
  unfold R.v39486, N.v39486.
  rewrite ?node_39484.
  rewrite ?node_39485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39487 (s : N.State) (i : N.Inputs) :
  R.v39487 (state s) (inputs i) = Zmod.unsigned (N.v39487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39487 s i)) at 1.
  unfold R.v39487, N.v39487.
  unfold R.v16463, N.v16463.
  rewrite ?node_39486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39488 (s : N.State) (i : N.Inputs) :
  R.v39488 (state s) (inputs i) = Zmod.unsigned (N.v39488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39488 s i)) at 1.
  unfold R.v39488, N.v39488.
  rewrite ?node_6934.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39489 (s : N.State) (i : N.Inputs) :
  R.v39489 (state s) (inputs i) = Zmod.unsigned (N.v39489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39489 s i)) at 1.
  unfold R.v39489, N.v39489.
  unfold R.v6, N.v6.
  rewrite ?node_7046.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39490 (s : N.State) (i : N.Inputs) :
  R.v39490 (state s) (inputs i) = Zmod.unsigned (N.v39490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39490 s i)) at 1.
  unfold R.v39490, N.v39490.
  rewrite ?node_39488.
  rewrite ?node_39489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39491 (s : N.State) (i : N.Inputs) :
  R.v39491 (state s) (inputs i) = Zmod.unsigned (N.v39491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39491 s i)) at 1.
  unfold R.v39491, N.v39491.
  rewrite ?node_39487.
  rewrite ?node_39490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39492 (s : N.State) (i : N.Inputs) :
  R.v39492 (state s) (inputs i) = Zmod.unsigned (N.v39492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39492 s i)) at 1.
  unfold R.v39492, N.v39492.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39493 (s : N.State) (i : N.Inputs) :
  R.v39493 (state s) (inputs i) = Zmod.unsigned (N.v39493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39493 s i)) at 1.
  unfold R.v39493, N.v39493.
  rewrite ?node_7000.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39494 (s : N.State) (i : N.Inputs) :
  R.v39494 (state s) (inputs i) = Zmod.unsigned (N.v39494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39494 s i)) at 1.
  unfold R.v39494, N.v39494.
  rewrite ?node_6996.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39495 (s : N.State) (i : N.Inputs) :
  R.v39495 (state s) (inputs i) = Zmod.unsigned (N.v39495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39495 s i)) at 1.
  unfold R.v39495, N.v39495.
  rewrite ?node_6988.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39496 (s : N.State) (i : N.Inputs) :
  R.v39496 (state s) (inputs i) = Zmod.unsigned (N.v39496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39496 s i)) at 1.
  unfold R.v39496, N.v39496.
  unfold R.v6, N.v6.
  rewrite ?node_6980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39497 (s : N.State) (i : N.Inputs) :
  R.v39497 (state s) (inputs i) = Zmod.unsigned (N.v39497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39497 s i)) at 1.
  unfold R.v39497, N.v39497.
  unfold R.v6, N.v6.
  rewrite ?node_6973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39498 (s : N.State) (i : N.Inputs) :
  R.v39498 (state s) (inputs i) = Zmod.unsigned (N.v39498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39498 s i)) at 1.
  unfold R.v39498, N.v39498.
  rewrite ?node_39496.
  rewrite ?node_39497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39499 (s : N.State) (i : N.Inputs) :
  R.v39499 (state s) (inputs i) = Zmod.unsigned (N.v39499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39499 s i)) at 1.
  unfold R.v39499, N.v39499.
  unfold R.v16484, N.v16484.
  rewrite ?node_39498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39500 (s : N.State) (i : N.Inputs) :
  R.v39500 (state s) (inputs i) = Zmod.unsigned (N.v39500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39500 s i)) at 1.
  unfold R.v39500, N.v39500.
  rewrite ?node_39493.
  rewrite ?node_39494.
  rewrite ?node_39495.
  rewrite ?node_39499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39501 (s : N.State) (i : N.Inputs) :
  R.v39501 (state s) (inputs i) = Zmod.unsigned (N.v39501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39501 s i)) at 1.
  unfold R.v39501, N.v39501.
  unfold R.v6, N.v6.
  rewrite ?node_39500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39502 (s : N.State) (i : N.Inputs) :
  R.v39502 (state s) (inputs i) = Zmod.unsigned (N.v39502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39502 s i)) at 1.
  unfold R.v39502, N.v39502.
  rewrite ?node_7001.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39503 (s : N.State) (i : N.Inputs) :
  R.v39503 (state s) (inputs i) = Zmod.unsigned (N.v39503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39503 s i)) at 1.
  unfold R.v39503, N.v39503.
  unfold R.v6, N.v6.
  rewrite ?node_7099.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39504 (s : N.State) (i : N.Inputs) :
  R.v39504 (state s) (inputs i) = Zmod.unsigned (N.v39504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39504 s i)) at 1.
  unfold R.v39504, N.v39504.
  unfold R.v6, N.v6.
  rewrite ?node_7136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39505 (s : N.State) (i : N.Inputs) :
  R.v39505 (state s) (inputs i) = Zmod.unsigned (N.v39505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39505 s i)) at 1.
  unfold R.v39505, N.v39505.
  rewrite ?node_39502.
  rewrite ?node_39503.
  rewrite ?node_39504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39506 (s : N.State) (i : N.Inputs) :
  R.v39506 (state s) (inputs i) = Zmod.unsigned (N.v39506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39506 s i)) at 1.
  unfold R.v39506, N.v39506.
  rewrite ?node_39501.
  rewrite ?node_39505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39507 (s : N.State) (i : N.Inputs) :
  R.v39507 (state s) (inputs i) = Zmod.unsigned (N.v39507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39507 s i)) at 1.
  unfold R.v39507, N.v39507.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39508 (s : N.State) (i : N.Inputs) :
  R.v39508 (state s) (inputs i) = Zmod.unsigned (N.v39508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39508 s i)) at 1.
  unfold R.v39508, N.v39508.
  rewrite ?node_6988.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39509 (s : N.State) (i : N.Inputs) :
  R.v39509 (state s) (inputs i) = Zmod.unsigned (N.v39509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39509 s i)) at 1.
  unfold R.v39509, N.v39509.
  unfold R.v6, N.v6.
  rewrite ?node_6980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39510 (s : N.State) (i : N.Inputs) :
  R.v39510 (state s) (inputs i) = Zmod.unsigned (N.v39510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39510 s i)) at 1.
  unfold R.v39510, N.v39510.
  unfold R.v6, N.v6.
  rewrite ?node_6973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39511 (s : N.State) (i : N.Inputs) :
  R.v39511 (state s) (inputs i) = Zmod.unsigned (N.v39511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39511 s i)) at 1.
  unfold R.v39511, N.v39511.
  rewrite ?node_39509.
  rewrite ?node_39510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39512 (s : N.State) (i : N.Inputs) :
  R.v39512 (state s) (inputs i) = Zmod.unsigned (N.v39512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39512 s i)) at 1.
  unfold R.v39512, N.v39512.
  unfold R.v16484, N.v16484.
  rewrite ?node_39511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39513 (s : N.State) (i : N.Inputs) :
  R.v39513 (state s) (inputs i) = Zmod.unsigned (N.v39513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39513 s i)) at 1.
  unfold R.v39513, N.v39513.
  rewrite ?node_39508.
  rewrite ?node_39512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39514 (s : N.State) (i : N.Inputs) :
  R.v39514 (state s) (inputs i) = Zmod.unsigned (N.v39514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39514 s i)) at 1.
  unfold R.v39514, N.v39514.
  unfold R.v6, N.v6.
  rewrite ?node_39513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39515 (s : N.State) (i : N.Inputs) :
  R.v39515 (state s) (inputs i) = Zmod.unsigned (N.v39515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39515 s i)) at 1.
  unfold R.v39515, N.v39515.
  rewrite ?node_6989.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39516 (s : N.State) (i : N.Inputs) :
  R.v39516 (state s) (inputs i) = Zmod.unsigned (N.v39516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39516 s i)) at 1.
  unfold R.v39516, N.v39516.
  unfold R.v6, N.v6.
  rewrite ?node_7099.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39517 (s : N.State) (i : N.Inputs) :
  R.v39517 (state s) (inputs i) = Zmod.unsigned (N.v39517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39517 s i)) at 1.
  unfold R.v39517, N.v39517.
  rewrite ?node_39515.
  rewrite ?node_39516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39518 (s : N.State) (i : N.Inputs) :
  R.v39518 (state s) (inputs i) = Zmod.unsigned (N.v39518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39518 s i)) at 1.
  unfold R.v39518, N.v39518.
  rewrite ?node_39514.
  rewrite ?node_39517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39519 (s : N.State) (i : N.Inputs) :
  R.v39519 (state s) (inputs i) = Zmod.unsigned (N.v39519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39519 s i)) at 1.
  unfold R.v39519, N.v39519.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39520 (s : N.State) (i : N.Inputs) :
  R.v39520 (state s) (inputs i) = Zmod.unsigned (N.v39520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39520 s i)) at 1.
  unfold R.v39520, N.v39520.
  rewrite ?node_7000.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39521 (s : N.State) (i : N.Inputs) :
  R.v39521 (state s) (inputs i) = Zmod.unsigned (N.v39521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39521 s i)) at 1.
  unfold R.v39521, N.v39521.
  unfold R.v6, N.v6.
  rewrite ?node_6996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39522 (s : N.State) (i : N.Inputs) :
  R.v39522 (state s) (inputs i) = Zmod.unsigned (N.v39522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39522 s i)) at 1.
  unfold R.v39522, N.v39522.
  unfold R.v6, N.v6.
  rewrite ?node_6989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39523 (s : N.State) (i : N.Inputs) :
  R.v39523 (state s) (inputs i) = Zmod.unsigned (N.v39523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39523 s i)) at 1.
  unfold R.v39523, N.v39523.
  rewrite ?node_39521.
  rewrite ?node_39522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39524 (s : N.State) (i : N.Inputs) :
  R.v39524 (state s) (inputs i) = Zmod.unsigned (N.v39524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39524 s i)) at 1.
  unfold R.v39524, N.v39524.
  unfold R.v16484, N.v16484.
  rewrite ?node_39523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39525 (s : N.State) (i : N.Inputs) :
  R.v39525 (state s) (inputs i) = Zmod.unsigned (N.v39525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39525 s i)) at 1.
  unfold R.v39525, N.v39525.
  rewrite ?node_39520.
  rewrite ?node_39524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39526 (s : N.State) (i : N.Inputs) :
  R.v39526 (state s) (inputs i) = Zmod.unsigned (N.v39526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39526 s i)) at 1.
  unfold R.v39526, N.v39526.
  unfold R.v6, N.v6.
  rewrite ?node_39525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39527 (s : N.State) (i : N.Inputs) :
  R.v39527 (state s) (inputs i) = Zmod.unsigned (N.v39527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39527 s i)) at 1.
  unfold R.v39527, N.v39527.
  rewrite ?node_7001.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39528 (s : N.State) (i : N.Inputs) :
  R.v39528 (state s) (inputs i) = Zmod.unsigned (N.v39528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39528 s i)) at 1.
  unfold R.v39528, N.v39528.
  unfold R.v6, N.v6.
  rewrite ?node_7136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39529 (s : N.State) (i : N.Inputs) :
  R.v39529 (state s) (inputs i) = Zmod.unsigned (N.v39529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39529 s i)) at 1.
  unfold R.v39529, N.v39529.
  rewrite ?node_39527.
  rewrite ?node_39528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39530 (s : N.State) (i : N.Inputs) :
  R.v39530 (state s) (inputs i) = Zmod.unsigned (N.v39530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39530 s i)) at 1.
  unfold R.v39530, N.v39530.
  rewrite ?node_39526.
  rewrite ?node_39529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39531 (s : N.State) (i : N.Inputs) :
  R.v39531 (state s) (inputs i) = Zmod.unsigned (N.v39531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39531 s i)) at 1.
  unfold R.v39531, N.v39531.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39532 (s : N.State) (i : N.Inputs) :
  R.v39532 (state s) (inputs i) = Zmod.unsigned (N.v39532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39532 s i)) at 1.
  unfold R.v39532, N.v39532.
  rewrite ?node_7020.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39533 (s : N.State) (i : N.Inputs) :
  R.v39533 (state s) (inputs i) = Zmod.unsigned (N.v39533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39533 s i)) at 1.
  unfold R.v39533, N.v39533.
  rewrite ?node_7016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39534 (s : N.State) (i : N.Inputs) :
  R.v39534 (state s) (inputs i) = Zmod.unsigned (N.v39534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39534 s i)) at 1.
  unfold R.v39534, N.v39534.
  rewrite ?node_7012.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39535 (s : N.State) (i : N.Inputs) :
  R.v39535 (state s) (inputs i) = Zmod.unsigned (N.v39535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39535 s i)) at 1.
  unfold R.v39535, N.v39535.
  unfold R.v6, N.v6.
  rewrite !state_r438_nr_5F438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r438_nr_5F438 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39536 (s : N.State) (i : N.Inputs) :
  R.v39536 (state s) (inputs i) = Zmod.unsigned (N.v39536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39536 s i)) at 1.
  unfold R.v39536, N.v39536.
  unfold R.v6, N.v6.
  rewrite ?node_7008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39537 (s : N.State) (i : N.Inputs) :
  R.v39537 (state s) (inputs i) = Zmod.unsigned (N.v39537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39537 s i)) at 1.
  unfold R.v39537, N.v39537.
  rewrite ?node_39535.
  rewrite ?node_39536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39538 (s : N.State) (i : N.Inputs) :
  R.v39538 (state s) (inputs i) = Zmod.unsigned (N.v39538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39538 s i)) at 1.
  unfold R.v39538, N.v39538.
  unfold R.v16484, N.v16484.
  rewrite ?node_39537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39539 (s : N.State) (i : N.Inputs) :
  R.v39539 (state s) (inputs i) = Zmod.unsigned (N.v39539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39539 s i)) at 1.
  unfold R.v39539, N.v39539.
  rewrite ?node_39532.
  rewrite ?node_39533.
  rewrite ?node_39534.
  rewrite ?node_39538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39540 (s : N.State) (i : N.Inputs) :
  R.v39540 (state s) (inputs i) = Zmod.unsigned (N.v39540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39540 s i)) at 1.
  unfold R.v39540, N.v39540.
  unfold R.v6, N.v6.
  rewrite ?node_39539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39541 (s : N.State) (i : N.Inputs) :
  R.v39541 (state s) (inputs i) = Zmod.unsigned (N.v39541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39541 s i)) at 1.
  unfold R.v39541, N.v39541.
  rewrite ?node_7021.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39542 (s : N.State) (i : N.Inputs) :
  R.v39542 (state s) (inputs i) = Zmod.unsigned (N.v39542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39542 s i)) at 1.
  unfold R.v39542, N.v39542.
  unfold R.v6, N.v6.
  rewrite ?node_7119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39543 (s : N.State) (i : N.Inputs) :
  R.v39543 (state s) (inputs i) = Zmod.unsigned (N.v39543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39543 s i)) at 1.
  unfold R.v39543, N.v39543.
  unfold R.v6, N.v6.
  rewrite ?node_7144.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39544 (s : N.State) (i : N.Inputs) :
  R.v39544 (state s) (inputs i) = Zmod.unsigned (N.v39544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39544 s i)) at 1.
  unfold R.v39544, N.v39544.
  rewrite ?node_39541.
  rewrite ?node_39542.
  rewrite ?node_39543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39545 (s : N.State) (i : N.Inputs) :
  R.v39545 (state s) (inputs i) = Zmod.unsigned (N.v39545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39545 s i)) at 1.
  unfold R.v39545, N.v39545.
  rewrite ?node_39540.
  rewrite ?node_39544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39546 (s : N.State) (i : N.Inputs) :
  R.v39546 (state s) (inputs i) = Zmod.unsigned (N.v39546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39546 s i)) at 1.
  unfold R.v39546, N.v39546.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39547 (s : N.State) (i : N.Inputs) :
  R.v39547 (state s) (inputs i) = Zmod.unsigned (N.v39547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39547 s i)) at 1.
  unfold R.v39547, N.v39547.
  rewrite ?node_7012.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39548 (s : N.State) (i : N.Inputs) :
  R.v39548 (state s) (inputs i) = Zmod.unsigned (N.v39548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39548 s i)) at 1.
  unfold R.v39548, N.v39548.
  unfold R.v6, N.v6.
  rewrite !state_r438_nr_5F438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r438_nr_5F438 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39549 (s : N.State) (i : N.Inputs) :
  R.v39549 (state s) (inputs i) = Zmod.unsigned (N.v39549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39549 s i)) at 1.
  unfold R.v39549, N.v39549.
  unfold R.v6, N.v6.
  rewrite ?node_7008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39550 (s : N.State) (i : N.Inputs) :
  R.v39550 (state s) (inputs i) = Zmod.unsigned (N.v39550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39550 s i)) at 1.
  unfold R.v39550, N.v39550.
  rewrite ?node_39548.
  rewrite ?node_39549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39551 (s : N.State) (i : N.Inputs) :
  R.v39551 (state s) (inputs i) = Zmod.unsigned (N.v39551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39551 s i)) at 1.
  unfold R.v39551, N.v39551.
  unfold R.v16484, N.v16484.
  rewrite ?node_39550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39552 (s : N.State) (i : N.Inputs) :
  R.v39552 (state s) (inputs i) = Zmod.unsigned (N.v39552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39552 s i)) at 1.
  unfold R.v39552, N.v39552.
  rewrite ?node_39547.
  rewrite ?node_39551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39553 (s : N.State) (i : N.Inputs) :
  R.v39553 (state s) (inputs i) = Zmod.unsigned (N.v39553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39553 s i)) at 1.
  unfold R.v39553, N.v39553.
  unfold R.v6, N.v6.
  rewrite ?node_39552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39554 (s : N.State) (i : N.Inputs) :
  R.v39554 (state s) (inputs i) = Zmod.unsigned (N.v39554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39554 s i)) at 1.
  unfold R.v39554, N.v39554.
  rewrite ?node_7013.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39555 (s : N.State) (i : N.Inputs) :
  R.v39555 (state s) (inputs i) = Zmod.unsigned (N.v39555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39555 s i)) at 1.
  unfold R.v39555, N.v39555.
  unfold R.v6, N.v6.
  rewrite ?node_7119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39556 (s : N.State) (i : N.Inputs) :
  R.v39556 (state s) (inputs i) = Zmod.unsigned (N.v39556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39556 s i)) at 1.
  unfold R.v39556, N.v39556.
  rewrite ?node_39554.
  rewrite ?node_39555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39557 (s : N.State) (i : N.Inputs) :
  R.v39557 (state s) (inputs i) = Zmod.unsigned (N.v39557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39557 s i)) at 1.
  unfold R.v39557, N.v39557.
  rewrite ?node_39553.
  rewrite ?node_39556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39558 (s : N.State) (i : N.Inputs) :
  R.v39558 (state s) (inputs i) = Zmod.unsigned (N.v39558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39558 s i)) at 1.
  unfold R.v39558, N.v39558.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39559 (s : N.State) (i : N.Inputs) :
  R.v39559 (state s) (inputs i) = Zmod.unsigned (N.v39559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39559 s i)) at 1.
  unfold R.v39559, N.v39559.
  rewrite ?node_7020.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39560 (s : N.State) (i : N.Inputs) :
  R.v39560 (state s) (inputs i) = Zmod.unsigned (N.v39560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39560 s i)) at 1.
  unfold R.v39560, N.v39560.
  unfold R.v6, N.v6.
  rewrite ?node_7016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39561 (s : N.State) (i : N.Inputs) :
  R.v39561 (state s) (inputs i) = Zmod.unsigned (N.v39561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39561 s i)) at 1.
  unfold R.v39561, N.v39561.
  unfold R.v6, N.v6.
  rewrite ?node_7013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39562 (s : N.State) (i : N.Inputs) :
  R.v39562 (state s) (inputs i) = Zmod.unsigned (N.v39562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39562 s i)) at 1.
  unfold R.v39562, N.v39562.
  rewrite ?node_39560.
  rewrite ?node_39561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39563 (s : N.State) (i : N.Inputs) :
  R.v39563 (state s) (inputs i) = Zmod.unsigned (N.v39563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39563 s i)) at 1.
  unfold R.v39563, N.v39563.
  unfold R.v16484, N.v16484.
  rewrite ?node_39562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39564 (s : N.State) (i : N.Inputs) :
  R.v39564 (state s) (inputs i) = Zmod.unsigned (N.v39564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39564 s i)) at 1.
  unfold R.v39564, N.v39564.
  rewrite ?node_39559.
  rewrite ?node_39563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39565 (s : N.State) (i : N.Inputs) :
  R.v39565 (state s) (inputs i) = Zmod.unsigned (N.v39565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39565 s i)) at 1.
  unfold R.v39565, N.v39565.
  unfold R.v6, N.v6.
  rewrite ?node_39564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39566 (s : N.State) (i : N.Inputs) :
  R.v39566 (state s) (inputs i) = Zmod.unsigned (N.v39566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39566 s i)) at 1.
  unfold R.v39566, N.v39566.
  rewrite ?node_7021.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39567 (s : N.State) (i : N.Inputs) :
  R.v39567 (state s) (inputs i) = Zmod.unsigned (N.v39567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39567 s i)) at 1.
  unfold R.v39567, N.v39567.
  unfold R.v6, N.v6.
  rewrite ?node_7144.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39568 (s : N.State) (i : N.Inputs) :
  R.v39568 (state s) (inputs i) = Zmod.unsigned (N.v39568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39568 s i)) at 1.
  unfold R.v39568, N.v39568.
  rewrite ?node_39566.
  rewrite ?node_39567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39569 (s : N.State) (i : N.Inputs) :
  R.v39569 (state s) (inputs i) = Zmod.unsigned (N.v39569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39569 s i)) at 1.
  unfold R.v39569, N.v39569.
  rewrite ?node_39565.
  rewrite ?node_39568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39570 (s : N.State) (i : N.Inputs) :
  R.v39570 (state s) (inputs i) = Zmod.unsigned (N.v39570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39570 s i)) at 1.
  unfold R.v39570, N.v39570.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39571 (s : N.State) (i : N.Inputs) :
  R.v39571 (state s) (inputs i) = Zmod.unsigned (N.v39571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39571 s i)) at 1.
  unfold R.v39571, N.v39571.
  rewrite ?node_7032.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39572 (s : N.State) (i : N.Inputs) :
  R.v39572 (state s) (inputs i) = Zmod.unsigned (N.v39572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39572 s i)) at 1.
  unfold R.v39572, N.v39572.
  unfold R.v6, N.v6.
  rewrite ?node_7028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39573 (s : N.State) (i : N.Inputs) :
  R.v39573 (state s) (inputs i) = Zmod.unsigned (N.v39573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39573 s i)) at 1.
  unfold R.v39573, N.v39573.
  unfold R.v6, N.v6.
  rewrite ?node_7025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39574 (s : N.State) (i : N.Inputs) :
  R.v39574 (state s) (inputs i) = Zmod.unsigned (N.v39574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39574 s i)) at 1.
  unfold R.v39574, N.v39574.
  rewrite ?node_39572.
  rewrite ?node_39573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39575 (s : N.State) (i : N.Inputs) :
  R.v39575 (state s) (inputs i) = Zmod.unsigned (N.v39575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39575 s i)) at 1.
  unfold R.v39575, N.v39575.
  unfold R.v16484, N.v16484.
  rewrite ?node_39574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39576 (s : N.State) (i : N.Inputs) :
  R.v39576 (state s) (inputs i) = Zmod.unsigned (N.v39576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39576 s i)) at 1.
  unfold R.v39576, N.v39576.
  rewrite ?node_39571.
  rewrite ?node_39575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39577 (s : N.State) (i : N.Inputs) :
  R.v39577 (state s) (inputs i) = Zmod.unsigned (N.v39577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39577 s i)) at 1.
  unfold R.v39577, N.v39577.
  unfold R.v6, N.v6.
  rewrite ?node_39576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39578 (s : N.State) (i : N.Inputs) :
  R.v39578 (state s) (inputs i) = Zmod.unsigned (N.v39578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39578 s i)) at 1.
  unfold R.v39578, N.v39578.
  rewrite ?node_7033.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39579 (s : N.State) (i : N.Inputs) :
  R.v39579 (state s) (inputs i) = Zmod.unsigned (N.v39579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39579 s i)) at 1.
  unfold R.v39579, N.v39579.
  unfold R.v6, N.v6.
  rewrite ?node_7147.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39580 (s : N.State) (i : N.Inputs) :
  R.v39580 (state s) (inputs i) = Zmod.unsigned (N.v39580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39580 s i)) at 1.
  unfold R.v39580, N.v39580.
  rewrite ?node_39578.
  rewrite ?node_39579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39581 (s : N.State) (i : N.Inputs) :
  R.v39581 (state s) (inputs i) = Zmod.unsigned (N.v39581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39581 s i)) at 1.
  unfold R.v39581, N.v39581.
  rewrite ?node_39577.
  rewrite ?node_39580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39582 (s : N.State) (i : N.Inputs) :
  R.v39582 (state s) (inputs i) = Zmod.unsigned (N.v39582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39582 s i)) at 1.
  unfold R.v39582, N.v39582.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39583 (s : N.State) (i : N.Inputs) :
  R.v39583 (state s) (inputs i) = Zmod.unsigned (N.v39583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39583 s i)) at 1.
  unfold R.v39583, N.v39583.
  rewrite ?node_7099.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39584 (s : N.State) (i : N.Inputs) :
  R.v39584 (state s) (inputs i) = Zmod.unsigned (N.v39584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39584 s i)) at 1.
  unfold R.v39584, N.v39584.
  rewrite ?node_7095.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39585 (s : N.State) (i : N.Inputs) :
  R.v39585 (state s) (inputs i) = Zmod.unsigned (N.v39585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39585 s i)) at 1.
  unfold R.v39585, N.v39585.
  rewrite ?node_7087.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39586 (s : N.State) (i : N.Inputs) :
  R.v39586 (state s) (inputs i) = Zmod.unsigned (N.v39586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39586 s i)) at 1.
  unfold R.v39586, N.v39586.
  unfold R.v6, N.v6.
  rewrite ?node_7079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39587 (s : N.State) (i : N.Inputs) :
  R.v39587 (state s) (inputs i) = Zmod.unsigned (N.v39587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39587 s i)) at 1.
  unfold R.v39587, N.v39587.
  unfold R.v6, N.v6.
  rewrite ?node_7072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39588 (s : N.State) (i : N.Inputs) :
  R.v39588 (state s) (inputs i) = Zmod.unsigned (N.v39588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39588 s i)) at 1.
  unfold R.v39588, N.v39588.
  rewrite ?node_39586.
  rewrite ?node_39587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39589 (s : N.State) (i : N.Inputs) :
  R.v39589 (state s) (inputs i) = Zmod.unsigned (N.v39589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39589 s i)) at 1.
  unfold R.v39589, N.v39589.
  unfold R.v16484, N.v16484.
  rewrite ?node_39588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39590 (s : N.State) (i : N.Inputs) :
  R.v39590 (state s) (inputs i) = Zmod.unsigned (N.v39590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39590 s i)) at 1.
  unfold R.v39590, N.v39590.
  rewrite ?node_39583.
  rewrite ?node_39584.
  rewrite ?node_39585.
  rewrite ?node_39589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39591 (s : N.State) (i : N.Inputs) :
  R.v39591 (state s) (inputs i) = Zmod.unsigned (N.v39591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39591 s i)) at 1.
  unfold R.v39591, N.v39591.
  unfold R.v6, N.v6.
  rewrite ?node_39590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39592 (s : N.State) (i : N.Inputs) :
  R.v39592 (state s) (inputs i) = Zmod.unsigned (N.v39592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39592 s i)) at 1.
  unfold R.v39592, N.v39592.
  rewrite ?node_7100.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39593 (s : N.State) (i : N.Inputs) :
  R.v39593 (state s) (inputs i) = Zmod.unsigned (N.v39593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39593 s i)) at 1.
  unfold R.v39593, N.v39593.
  unfold R.v6, N.v6.
  rewrite ?node_7200.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39594 (s : N.State) (i : N.Inputs) :
  R.v39594 (state s) (inputs i) = Zmod.unsigned (N.v39594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39594 s i)) at 1.
  unfold R.v39594, N.v39594.
  unfold R.v6, N.v6.
  rewrite ?node_7238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39595 (s : N.State) (i : N.Inputs) :
  R.v39595 (state s) (inputs i) = Zmod.unsigned (N.v39595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39595 s i)) at 1.
  unfold R.v39595, N.v39595.
  rewrite ?node_39592.
  rewrite ?node_39593.
  rewrite ?node_39594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39596 (s : N.State) (i : N.Inputs) :
  R.v39596 (state s) (inputs i) = Zmod.unsigned (N.v39596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39596 s i)) at 1.
  unfold R.v39596, N.v39596.
  rewrite ?node_39591.
  rewrite ?node_39595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39597 (s : N.State) (i : N.Inputs) :
  R.v39597 (state s) (inputs i) = Zmod.unsigned (N.v39597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39597 s i)) at 1.
  unfold R.v39597, N.v39597.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39598 (s : N.State) (i : N.Inputs) :
  R.v39598 (state s) (inputs i) = Zmod.unsigned (N.v39598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39598 s i)) at 1.
  unfold R.v39598, N.v39598.
  rewrite ?node_7087.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39599 (s : N.State) (i : N.Inputs) :
  R.v39599 (state s) (inputs i) = Zmod.unsigned (N.v39599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39599 s i)) at 1.
  unfold R.v39599, N.v39599.
  unfold R.v6, N.v6.
  rewrite ?node_7079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39600 (s : N.State) (i : N.Inputs) :
  R.v39600 (state s) (inputs i) = Zmod.unsigned (N.v39600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39600 s i)) at 1.
  unfold R.v39600, N.v39600.
  unfold R.v6, N.v6.
  rewrite ?node_7072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39601 (s : N.State) (i : N.Inputs) :
  R.v39601 (state s) (inputs i) = Zmod.unsigned (N.v39601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39601 s i)) at 1.
  unfold R.v39601, N.v39601.
  rewrite ?node_39599.
  rewrite ?node_39600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39602 (s : N.State) (i : N.Inputs) :
  R.v39602 (state s) (inputs i) = Zmod.unsigned (N.v39602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39602 s i)) at 1.
  unfold R.v39602, N.v39602.
  unfold R.v16484, N.v16484.
  rewrite ?node_39601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39603 (s : N.State) (i : N.Inputs) :
  R.v39603 (state s) (inputs i) = Zmod.unsigned (N.v39603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39603 s i)) at 1.
  unfold R.v39603, N.v39603.
  rewrite ?node_39598.
  rewrite ?node_39602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39604 (s : N.State) (i : N.Inputs) :
  R.v39604 (state s) (inputs i) = Zmod.unsigned (N.v39604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39604 s i)) at 1.
  unfold R.v39604, N.v39604.
  unfold R.v6, N.v6.
  rewrite ?node_39603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39605 (s : N.State) (i : N.Inputs) :
  R.v39605 (state s) (inputs i) = Zmod.unsigned (N.v39605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39605 s i)) at 1.
  unfold R.v39605, N.v39605.
  rewrite ?node_7088.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39606 (s : N.State) (i : N.Inputs) :
  R.v39606 (state s) (inputs i) = Zmod.unsigned (N.v39606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39606 s i)) at 1.
  unfold R.v39606, N.v39606.
  unfold R.v6, N.v6.
  rewrite ?node_7200.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39607 (s : N.State) (i : N.Inputs) :
  R.v39607 (state s) (inputs i) = Zmod.unsigned (N.v39607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39607 s i)) at 1.
  unfold R.v39607, N.v39607.
  rewrite ?node_39605.
  rewrite ?node_39606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39608 (s : N.State) (i : N.Inputs) :
  R.v39608 (state s) (inputs i) = Zmod.unsigned (N.v39608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39608 s i)) at 1.
  unfold R.v39608, N.v39608.
  rewrite ?node_39604.
  rewrite ?node_39607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39609 (s : N.State) (i : N.Inputs) :
  R.v39609 (state s) (inputs i) = Zmod.unsigned (N.v39609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39609 s i)) at 1.
  unfold R.v39609, N.v39609.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39610 (s : N.State) (i : N.Inputs) :
  R.v39610 (state s) (inputs i) = Zmod.unsigned (N.v39610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39610 s i)) at 1.
  unfold R.v39610, N.v39610.
  rewrite ?node_7099.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39611 (s : N.State) (i : N.Inputs) :
  R.v39611 (state s) (inputs i) = Zmod.unsigned (N.v39611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39611 s i)) at 1.
  unfold R.v39611, N.v39611.
  unfold R.v6, N.v6.
  rewrite ?node_7095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39612 (s : N.State) (i : N.Inputs) :
  R.v39612 (state s) (inputs i) = Zmod.unsigned (N.v39612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39612 s i)) at 1.
  unfold R.v39612, N.v39612.
  unfold R.v6, N.v6.
  rewrite ?node_7088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39613 (s : N.State) (i : N.Inputs) :
  R.v39613 (state s) (inputs i) = Zmod.unsigned (N.v39613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39613 s i)) at 1.
  unfold R.v39613, N.v39613.
  rewrite ?node_39611.
  rewrite ?node_39612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39614 (s : N.State) (i : N.Inputs) :
  R.v39614 (state s) (inputs i) = Zmod.unsigned (N.v39614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39614 s i)) at 1.
  unfold R.v39614, N.v39614.
  unfold R.v16484, N.v16484.
  rewrite ?node_39613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39615 (s : N.State) (i : N.Inputs) :
  R.v39615 (state s) (inputs i) = Zmod.unsigned (N.v39615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39615 s i)) at 1.
  unfold R.v39615, N.v39615.
  rewrite ?node_39610.
  rewrite ?node_39614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39616 (s : N.State) (i : N.Inputs) :
  R.v39616 (state s) (inputs i) = Zmod.unsigned (N.v39616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39616 s i)) at 1.
  unfold R.v39616, N.v39616.
  unfold R.v6, N.v6.
  rewrite ?node_39615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39617 (s : N.State) (i : N.Inputs) :
  R.v39617 (state s) (inputs i) = Zmod.unsigned (N.v39617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39617 s i)) at 1.
  unfold R.v39617, N.v39617.
  rewrite ?node_7100.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39618 (s : N.State) (i : N.Inputs) :
  R.v39618 (state s) (inputs i) = Zmod.unsigned (N.v39618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39618 s i)) at 1.
  unfold R.v39618, N.v39618.
  unfold R.v6, N.v6.
  rewrite ?node_7238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39619 (s : N.State) (i : N.Inputs) :
  R.v39619 (state s) (inputs i) = Zmod.unsigned (N.v39619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39619 s i)) at 1.
  unfold R.v39619, N.v39619.
  rewrite ?node_39617.
  rewrite ?node_39618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39620 (s : N.State) (i : N.Inputs) :
  R.v39620 (state s) (inputs i) = Zmod.unsigned (N.v39620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39620 s i)) at 1.
  unfold R.v39620, N.v39620.
  rewrite ?node_39616.
  rewrite ?node_39619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39621 (s : N.State) (i : N.Inputs) :
  R.v39621 (state s) (inputs i) = Zmod.unsigned (N.v39621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39621 s i)) at 1.
  unfold R.v39621, N.v39621.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39622 (s : N.State) (i : N.Inputs) :
  R.v39622 (state s) (inputs i) = Zmod.unsigned (N.v39622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39622 s i)) at 1.
  unfold R.v39622, N.v39622.
  rewrite ?node_7119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39623 (s : N.State) (i : N.Inputs) :
  R.v39623 (state s) (inputs i) = Zmod.unsigned (N.v39623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39623 s i)) at 1.
  unfold R.v39623, N.v39623.
  rewrite ?node_7115.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39624 (s : N.State) (i : N.Inputs) :
  R.v39624 (state s) (inputs i) = Zmod.unsigned (N.v39624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39624 s i)) at 1.
  unfold R.v39624, N.v39624.
  rewrite ?node_7111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39625 (s : N.State) (i : N.Inputs) :
  R.v39625 (state s) (inputs i) = Zmod.unsigned (N.v39625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39625 s i)) at 1.
  unfold R.v39625, N.v39625.
  unfold R.v6, N.v6.
  rewrite !state_r459_nr_5F459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r459_nr_5F459 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39626 (s : N.State) (i : N.Inputs) :
  R.v39626 (state s) (inputs i) = Zmod.unsigned (N.v39626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39626 s i)) at 1.
  unfold R.v39626, N.v39626.
  unfold R.v6, N.v6.
  rewrite ?node_7107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39627 (s : N.State) (i : N.Inputs) :
  R.v39627 (state s) (inputs i) = Zmod.unsigned (N.v39627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39627 s i)) at 1.
  unfold R.v39627, N.v39627.
  rewrite ?node_39625.
  rewrite ?node_39626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39628 (s : N.State) (i : N.Inputs) :
  R.v39628 (state s) (inputs i) = Zmod.unsigned (N.v39628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39628 s i)) at 1.
  unfold R.v39628, N.v39628.
  unfold R.v16484, N.v16484.
  rewrite ?node_39627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39629 (s : N.State) (i : N.Inputs) :
  R.v39629 (state s) (inputs i) = Zmod.unsigned (N.v39629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39629 s i)) at 1.
  unfold R.v39629, N.v39629.
  rewrite ?node_39622.
  rewrite ?node_39623.
  rewrite ?node_39624.
  rewrite ?node_39628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39630 (s : N.State) (i : N.Inputs) :
  R.v39630 (state s) (inputs i) = Zmod.unsigned (N.v39630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39630 s i)) at 1.
  unfold R.v39630, N.v39630.
  unfold R.v6, N.v6.
  rewrite ?node_39629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39631 (s : N.State) (i : N.Inputs) :
  R.v39631 (state s) (inputs i) = Zmod.unsigned (N.v39631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39631 s i)) at 1.
  unfold R.v39631, N.v39631.
  rewrite ?node_7120.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39632 (s : N.State) (i : N.Inputs) :
  R.v39632 (state s) (inputs i) = Zmod.unsigned (N.v39632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39632 s i)) at 1.
  unfold R.v39632, N.v39632.
  unfold R.v6, N.v6.
  rewrite ?node_7221.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39633 (s : N.State) (i : N.Inputs) :
  R.v39633 (state s) (inputs i) = Zmod.unsigned (N.v39633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39633 s i)) at 1.
  unfold R.v39633, N.v39633.
  unfold R.v6, N.v6.
  rewrite ?node_7246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39634 (s : N.State) (i : N.Inputs) :
  R.v39634 (state s) (inputs i) = Zmod.unsigned (N.v39634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39634 s i)) at 1.
  unfold R.v39634, N.v39634.
  rewrite ?node_39631.
  rewrite ?node_39632.
  rewrite ?node_39633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39635 (s : N.State) (i : N.Inputs) :
  R.v39635 (state s) (inputs i) = Zmod.unsigned (N.v39635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39635 s i)) at 1.
  unfold R.v39635, N.v39635.
  rewrite ?node_39630.
  rewrite ?node_39634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39636 (s : N.State) (i : N.Inputs) :
  R.v39636 (state s) (inputs i) = Zmod.unsigned (N.v39636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39636 s i)) at 1.
  unfold R.v39636, N.v39636.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39637 (s : N.State) (i : N.Inputs) :
  R.v39637 (state s) (inputs i) = Zmod.unsigned (N.v39637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39637 s i)) at 1.
  unfold R.v39637, N.v39637.
  rewrite ?node_7111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39638 (s : N.State) (i : N.Inputs) :
  R.v39638 (state s) (inputs i) = Zmod.unsigned (N.v39638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39638 s i)) at 1.
  unfold R.v39638, N.v39638.
  unfold R.v6, N.v6.
  rewrite !state_r459_nr_5F459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r459_nr_5F459 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39639 (s : N.State) (i : N.Inputs) :
  R.v39639 (state s) (inputs i) = Zmod.unsigned (N.v39639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39639 s i)) at 1.
  unfold R.v39639, N.v39639.
  unfold R.v6, N.v6.
  rewrite ?node_7107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39640 (s : N.State) (i : N.Inputs) :
  R.v39640 (state s) (inputs i) = Zmod.unsigned (N.v39640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39640 s i)) at 1.
  unfold R.v39640, N.v39640.
  rewrite ?node_39638.
  rewrite ?node_39639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39641 (s : N.State) (i : N.Inputs) :
  R.v39641 (state s) (inputs i) = Zmod.unsigned (N.v39641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39641 s i)) at 1.
  unfold R.v39641, N.v39641.
  unfold R.v16484, N.v16484.
  rewrite ?node_39640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39642 (s : N.State) (i : N.Inputs) :
  R.v39642 (state s) (inputs i) = Zmod.unsigned (N.v39642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39642 s i)) at 1.
  unfold R.v39642, N.v39642.
  rewrite ?node_39637.
  rewrite ?node_39641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39643 (s : N.State) (i : N.Inputs) :
  R.v39643 (state s) (inputs i) = Zmod.unsigned (N.v39643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39643 s i)) at 1.
  unfold R.v39643, N.v39643.
  unfold R.v6, N.v6.
  rewrite ?node_39642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39644 (s : N.State) (i : N.Inputs) :
  R.v39644 (state s) (inputs i) = Zmod.unsigned (N.v39644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39644 s i)) at 1.
  unfold R.v39644, N.v39644.
  rewrite ?node_7112.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39645 (s : N.State) (i : N.Inputs) :
  R.v39645 (state s) (inputs i) = Zmod.unsigned (N.v39645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39645 s i)) at 1.
  unfold R.v39645, N.v39645.
  unfold R.v6, N.v6.
  rewrite ?node_7221.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39646 (s : N.State) (i : N.Inputs) :
  R.v39646 (state s) (inputs i) = Zmod.unsigned (N.v39646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39646 s i)) at 1.
  unfold R.v39646, N.v39646.
  rewrite ?node_39644.
  rewrite ?node_39645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39647 (s : N.State) (i : N.Inputs) :
  R.v39647 (state s) (inputs i) = Zmod.unsigned (N.v39647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39647 s i)) at 1.
  unfold R.v39647, N.v39647.
  rewrite ?node_39643.
  rewrite ?node_39646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39648 (s : N.State) (i : N.Inputs) :
  R.v39648 (state s) (inputs i) = Zmod.unsigned (N.v39648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39648 s i)) at 1.
  unfold R.v39648, N.v39648.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39649 (s : N.State) (i : N.Inputs) :
  R.v39649 (state s) (inputs i) = Zmod.unsigned (N.v39649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39649 s i)) at 1.
  unfold R.v39649, N.v39649.
  rewrite ?node_7119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39650 (s : N.State) (i : N.Inputs) :
  R.v39650 (state s) (inputs i) = Zmod.unsigned (N.v39650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39650 s i)) at 1.
  unfold R.v39650, N.v39650.
  unfold R.v6, N.v6.
  rewrite ?node_7115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39651 (s : N.State) (i : N.Inputs) :
  R.v39651 (state s) (inputs i) = Zmod.unsigned (N.v39651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39651 s i)) at 1.
  unfold R.v39651, N.v39651.
  unfold R.v6, N.v6.
  rewrite ?node_7112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39652 (s : N.State) (i : N.Inputs) :
  R.v39652 (state s) (inputs i) = Zmod.unsigned (N.v39652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39652 s i)) at 1.
  unfold R.v39652, N.v39652.
  rewrite ?node_39650.
  rewrite ?node_39651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39653 (s : N.State) (i : N.Inputs) :
  R.v39653 (state s) (inputs i) = Zmod.unsigned (N.v39653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39653 s i)) at 1.
  unfold R.v39653, N.v39653.
  unfold R.v16484, N.v16484.
  rewrite ?node_39652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39654 (s : N.State) (i : N.Inputs) :
  R.v39654 (state s) (inputs i) = Zmod.unsigned (N.v39654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39654 s i)) at 1.
  unfold R.v39654, N.v39654.
  rewrite ?node_39649.
  rewrite ?node_39653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39655 (s : N.State) (i : N.Inputs) :
  R.v39655 (state s) (inputs i) = Zmod.unsigned (N.v39655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39655 s i)) at 1.
  unfold R.v39655, N.v39655.
  unfold R.v6, N.v6.
  rewrite ?node_39654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39656 (s : N.State) (i : N.Inputs) :
  R.v39656 (state s) (inputs i) = Zmod.unsigned (N.v39656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39656 s i)) at 1.
  unfold R.v39656, N.v39656.
  rewrite ?node_7120.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39657 (s : N.State) (i : N.Inputs) :
  R.v39657 (state s) (inputs i) = Zmod.unsigned (N.v39657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39657 s i)) at 1.
  unfold R.v39657, N.v39657.
  unfold R.v6, N.v6.
  rewrite ?node_7246.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39658 (s : N.State) (i : N.Inputs) :
  R.v39658 (state s) (inputs i) = Zmod.unsigned (N.v39658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39658 s i)) at 1.
  unfold R.v39658, N.v39658.
  rewrite ?node_39656.
  rewrite ?node_39657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39659 (s : N.State) (i : N.Inputs) :
  R.v39659 (state s) (inputs i) = Zmod.unsigned (N.v39659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39659 s i)) at 1.
  unfold R.v39659, N.v39659.
  rewrite ?node_39655.
  rewrite ?node_39658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39660 (s : N.State) (i : N.Inputs) :
  R.v39660 (state s) (inputs i) = Zmod.unsigned (N.v39660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39660 s i)) at 1.
  unfold R.v39660, N.v39660.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39661 (s : N.State) (i : N.Inputs) :
  R.v39661 (state s) (inputs i) = Zmod.unsigned (N.v39661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39661 s i)) at 1.
  unfold R.v39661, N.v39661.
  rewrite ?node_7131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39662 (s : N.State) (i : N.Inputs) :
  R.v39662 (state s) (inputs i) = Zmod.unsigned (N.v39662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39662 s i)) at 1.
  unfold R.v39662, N.v39662.
  unfold R.v6, N.v6.
  rewrite ?node_7127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39663 (s : N.State) (i : N.Inputs) :
  R.v39663 (state s) (inputs i) = Zmod.unsigned (N.v39663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39663 s i)) at 1.
  unfold R.v39663, N.v39663.
  unfold R.v6, N.v6.
  rewrite ?node_7124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39664 (s : N.State) (i : N.Inputs) :
  R.v39664 (state s) (inputs i) = Zmod.unsigned (N.v39664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39664 s i)) at 1.
  unfold R.v39664, N.v39664.
  rewrite ?node_39662.
  rewrite ?node_39663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39665 (s : N.State) (i : N.Inputs) :
  R.v39665 (state s) (inputs i) = Zmod.unsigned (N.v39665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39665 s i)) at 1.
  unfold R.v39665, N.v39665.
  unfold R.v16484, N.v16484.
  rewrite ?node_39664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39666 (s : N.State) (i : N.Inputs) :
  R.v39666 (state s) (inputs i) = Zmod.unsigned (N.v39666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39666 s i)) at 1.
  unfold R.v39666, N.v39666.
  rewrite ?node_39661.
  rewrite ?node_39665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39667 (s : N.State) (i : N.Inputs) :
  R.v39667 (state s) (inputs i) = Zmod.unsigned (N.v39667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39667 s i)) at 1.
  unfold R.v39667, N.v39667.
  unfold R.v6, N.v6.
  rewrite ?node_39666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39668 (s : N.State) (i : N.Inputs) :
  R.v39668 (state s) (inputs i) = Zmod.unsigned (N.v39668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39668 s i)) at 1.
  unfold R.v39668, N.v39668.
  rewrite ?node_7132.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39669 (s : N.State) (i : N.Inputs) :
  R.v39669 (state s) (inputs i) = Zmod.unsigned (N.v39669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39669 s i)) at 1.
  unfold R.v39669, N.v39669.
  unfold R.v6, N.v6.
  rewrite ?node_7249.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39670 (s : N.State) (i : N.Inputs) :
  R.v39670 (state s) (inputs i) = Zmod.unsigned (N.v39670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39670 s i)) at 1.
  unfold R.v39670, N.v39670.
  rewrite ?node_39668.
  rewrite ?node_39669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39671 (s : N.State) (i : N.Inputs) :
  R.v39671 (state s) (inputs i) = Zmod.unsigned (N.v39671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39671 s i)) at 1.
  unfold R.v39671, N.v39671.
  rewrite ?node_39667.
  rewrite ?node_39670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39672 (s : N.State) (i : N.Inputs) :
  R.v39672 (state s) (inputs i) = Zmod.unsigned (N.v39672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39672 s i)) at 1.
  unfold R.v39672, N.v39672.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39673 (s : N.State) (i : N.Inputs) :
  R.v39673 (state s) (inputs i) = Zmod.unsigned (N.v39673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39673 s i)) at 1.
  unfold R.v39673, N.v39673.
  rewrite ?node_7200.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39674 (s : N.State) (i : N.Inputs) :
  R.v39674 (state s) (inputs i) = Zmod.unsigned (N.v39674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39674 s i)) at 1.
  unfold R.v39674, N.v39674.
  rewrite ?node_7196.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39675 (s : N.State) (i : N.Inputs) :
  R.v39675 (state s) (inputs i) = Zmod.unsigned (N.v39675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39675 s i)) at 1.
  unfold R.v39675, N.v39675.
  rewrite ?node_7188.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39676 (s : N.State) (i : N.Inputs) :
  R.v39676 (state s) (inputs i) = Zmod.unsigned (N.v39676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39676 s i)) at 1.
  unfold R.v39676, N.v39676.
  unfold R.v6, N.v6.
  rewrite ?node_7180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39677 (s : N.State) (i : N.Inputs) :
  R.v39677 (state s) (inputs i) = Zmod.unsigned (N.v39677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39677 s i)) at 1.
  unfold R.v39677, N.v39677.
  unfold R.v6, N.v6.
  rewrite ?node_7173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39678 (s : N.State) (i : N.Inputs) :
  R.v39678 (state s) (inputs i) = Zmod.unsigned (N.v39678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39678 s i)) at 1.
  unfold R.v39678, N.v39678.
  rewrite ?node_39676.
  rewrite ?node_39677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39679 (s : N.State) (i : N.Inputs) :
  R.v39679 (state s) (inputs i) = Zmod.unsigned (N.v39679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39679 s i)) at 1.
  unfold R.v39679, N.v39679.
  unfold R.v16484, N.v16484.
  rewrite ?node_39678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39680 (s : N.State) (i : N.Inputs) :
  R.v39680 (state s) (inputs i) = Zmod.unsigned (N.v39680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39680 s i)) at 1.
  unfold R.v39680, N.v39680.
  rewrite ?node_39673.
  rewrite ?node_39674.
  rewrite ?node_39675.
  rewrite ?node_39679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39681 (s : N.State) (i : N.Inputs) :
  R.v39681 (state s) (inputs i) = Zmod.unsigned (N.v39681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39681 s i)) at 1.
  unfold R.v39681, N.v39681.
  unfold R.v6, N.v6.
  rewrite ?node_39680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39682 (s : N.State) (i : N.Inputs) :
  R.v39682 (state s) (inputs i) = Zmod.unsigned (N.v39682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39682 s i)) at 1.
  unfold R.v39682, N.v39682.
  rewrite ?node_7201.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39683 (s : N.State) (i : N.Inputs) :
  R.v39683 (state s) (inputs i) = Zmod.unsigned (N.v39683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39683 s i)) at 1.
  unfold R.v39683, N.v39683.
  unfold R.v6, N.v6.
  rewrite ?node_7302.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39684 (s : N.State) (i : N.Inputs) :
  R.v39684 (state s) (inputs i) = Zmod.unsigned (N.v39684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39684 s i)) at 1.
  unfold R.v39684, N.v39684.
  unfold R.v6, N.v6.
  rewrite ?node_7342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39685 (s : N.State) (i : N.Inputs) :
  R.v39685 (state s) (inputs i) = Zmod.unsigned (N.v39685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39685 s i)) at 1.
  unfold R.v39685, N.v39685.
  rewrite ?node_39682.
  rewrite ?node_39683.
  rewrite ?node_39684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39686 (s : N.State) (i : N.Inputs) :
  R.v39686 (state s) (inputs i) = Zmod.unsigned (N.v39686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39686 s i)) at 1.
  unfold R.v39686, N.v39686.
  rewrite ?node_39681.
  rewrite ?node_39685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39687 (s : N.State) (i : N.Inputs) :
  R.v39687 (state s) (inputs i) = Zmod.unsigned (N.v39687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39687 s i)) at 1.
  unfold R.v39687, N.v39687.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39688 (s : N.State) (i : N.Inputs) :
  R.v39688 (state s) (inputs i) = Zmod.unsigned (N.v39688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39688 s i)) at 1.
  unfold R.v39688, N.v39688.
  rewrite ?node_7188.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39689 (s : N.State) (i : N.Inputs) :
  R.v39689 (state s) (inputs i) = Zmod.unsigned (N.v39689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39689 s i)) at 1.
  unfold R.v39689, N.v39689.
  unfold R.v6, N.v6.
  rewrite ?node_7180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39690 (s : N.State) (i : N.Inputs) :
  R.v39690 (state s) (inputs i) = Zmod.unsigned (N.v39690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39690 s i)) at 1.
  unfold R.v39690, N.v39690.
  unfold R.v6, N.v6.
  rewrite ?node_7173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39691 (s : N.State) (i : N.Inputs) :
  R.v39691 (state s) (inputs i) = Zmod.unsigned (N.v39691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39691 s i)) at 1.
  unfold R.v39691, N.v39691.
  rewrite ?node_39689.
  rewrite ?node_39690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39692 (s : N.State) (i : N.Inputs) :
  R.v39692 (state s) (inputs i) = Zmod.unsigned (N.v39692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39692 s i)) at 1.
  unfold R.v39692, N.v39692.
  unfold R.v16484, N.v16484.
  rewrite ?node_39691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39693 (s : N.State) (i : N.Inputs) :
  R.v39693 (state s) (inputs i) = Zmod.unsigned (N.v39693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39693 s i)) at 1.
  unfold R.v39693, N.v39693.
  rewrite ?node_39688.
  rewrite ?node_39692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39694 (s : N.State) (i : N.Inputs) :
  R.v39694 (state s) (inputs i) = Zmod.unsigned (N.v39694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39694 s i)) at 1.
  unfold R.v39694, N.v39694.
  unfold R.v6, N.v6.
  rewrite ?node_39693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39695 (s : N.State) (i : N.Inputs) :
  R.v39695 (state s) (inputs i) = Zmod.unsigned (N.v39695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39695 s i)) at 1.
  unfold R.v39695, N.v39695.
  rewrite ?node_7189.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39696 (s : N.State) (i : N.Inputs) :
  R.v39696 (state s) (inputs i) = Zmod.unsigned (N.v39696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39696 s i)) at 1.
  unfold R.v39696, N.v39696.
  unfold R.v6, N.v6.
  rewrite ?node_7302.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39697 (s : N.State) (i : N.Inputs) :
  R.v39697 (state s) (inputs i) = Zmod.unsigned (N.v39697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39697 s i)) at 1.
  unfold R.v39697, N.v39697.
  rewrite ?node_39695.
  rewrite ?node_39696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39698 (s : N.State) (i : N.Inputs) :
  R.v39698 (state s) (inputs i) = Zmod.unsigned (N.v39698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39698 s i)) at 1.
  unfold R.v39698, N.v39698.
  rewrite ?node_39694.
  rewrite ?node_39697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39699 (s : N.State) (i : N.Inputs) :
  R.v39699 (state s) (inputs i) = Zmod.unsigned (N.v39699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39699 s i)) at 1.
  unfold R.v39699, N.v39699.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39700 (s : N.State) (i : N.Inputs) :
  R.v39700 (state s) (inputs i) = Zmod.unsigned (N.v39700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39700 s i)) at 1.
  unfold R.v39700, N.v39700.
  rewrite ?node_7200.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39701 (s : N.State) (i : N.Inputs) :
  R.v39701 (state s) (inputs i) = Zmod.unsigned (N.v39701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39701 s i)) at 1.
  unfold R.v39701, N.v39701.
  unfold R.v6, N.v6.
  rewrite ?node_7196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39702 (s : N.State) (i : N.Inputs) :
  R.v39702 (state s) (inputs i) = Zmod.unsigned (N.v39702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39702 s i)) at 1.
  unfold R.v39702, N.v39702.
  unfold R.v6, N.v6.
  rewrite ?node_7189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39703 (s : N.State) (i : N.Inputs) :
  R.v39703 (state s) (inputs i) = Zmod.unsigned (N.v39703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39703 s i)) at 1.
  unfold R.v39703, N.v39703.
  rewrite ?node_39701.
  rewrite ?node_39702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39704 (s : N.State) (i : N.Inputs) :
  R.v39704 (state s) (inputs i) = Zmod.unsigned (N.v39704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39704 s i)) at 1.
  unfold R.v39704, N.v39704.
  unfold R.v16484, N.v16484.
  rewrite ?node_39703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39705 (s : N.State) (i : N.Inputs) :
  R.v39705 (state s) (inputs i) = Zmod.unsigned (N.v39705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39705 s i)) at 1.
  unfold R.v39705, N.v39705.
  rewrite ?node_39700.
  rewrite ?node_39704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39706 (s : N.State) (i : N.Inputs) :
  R.v39706 (state s) (inputs i) = Zmod.unsigned (N.v39706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39706 s i)) at 1.
  unfold R.v39706, N.v39706.
  unfold R.v6, N.v6.
  rewrite ?node_39705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39707 (s : N.State) (i : N.Inputs) :
  R.v39707 (state s) (inputs i) = Zmod.unsigned (N.v39707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39707 s i)) at 1.
  unfold R.v39707, N.v39707.
  rewrite ?node_7201.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39708 (s : N.State) (i : N.Inputs) :
  R.v39708 (state s) (inputs i) = Zmod.unsigned (N.v39708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39708 s i)) at 1.
  unfold R.v39708, N.v39708.
  unfold R.v6, N.v6.
  rewrite ?node_7342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39709 (s : N.State) (i : N.Inputs) :
  R.v39709 (state s) (inputs i) = Zmod.unsigned (N.v39709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39709 s i)) at 1.
  unfold R.v39709, N.v39709.
  rewrite ?node_39707.
  rewrite ?node_39708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39710 (s : N.State) (i : N.Inputs) :
  R.v39710 (state s) (inputs i) = Zmod.unsigned (N.v39710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39710 s i)) at 1.
  unfold R.v39710, N.v39710.
  rewrite ?node_39706.
  rewrite ?node_39709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39711 (s : N.State) (i : N.Inputs) :
  R.v39711 (state s) (inputs i) = Zmod.unsigned (N.v39711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39711 s i)) at 1.
  unfold R.v39711, N.v39711.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39712 (s : N.State) (i : N.Inputs) :
  R.v39712 (state s) (inputs i) = Zmod.unsigned (N.v39712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39712 s i)) at 1.
  unfold R.v39712, N.v39712.
  rewrite ?node_7221.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39713 (s : N.State) (i : N.Inputs) :
  R.v39713 (state s) (inputs i) = Zmod.unsigned (N.v39713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39713 s i)) at 1.
  unfold R.v39713, N.v39713.
  rewrite ?node_7217.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39714 (s : N.State) (i : N.Inputs) :
  R.v39714 (state s) (inputs i) = Zmod.unsigned (N.v39714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39714 s i)) at 1.
  unfold R.v39714, N.v39714.
  rewrite ?node_7213.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39715 (s : N.State) (i : N.Inputs) :
  R.v39715 (state s) (inputs i) = Zmod.unsigned (N.v39715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39715 s i)) at 1.
  unfold R.v39715, N.v39715.
  unfold R.v6, N.v6.
  rewrite ?node_7209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39716 (s : N.State) (i : N.Inputs) :
  R.v39716 (state s) (inputs i) = Zmod.unsigned (N.v39716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39716 s i)) at 1.
  unfold R.v39716, N.v39716.
  unfold R.v6, N.v6.
  rewrite ?node_7208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39717 (s : N.State) (i : N.Inputs) :
  R.v39717 (state s) (inputs i) = Zmod.unsigned (N.v39717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39717 s i)) at 1.
  unfold R.v39717, N.v39717.
  rewrite ?node_39715.
  rewrite ?node_39716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39718 (s : N.State) (i : N.Inputs) :
  R.v39718 (state s) (inputs i) = Zmod.unsigned (N.v39718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39718 s i)) at 1.
  unfold R.v39718, N.v39718.
  unfold R.v16484, N.v16484.
  rewrite ?node_39717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39719 (s : N.State) (i : N.Inputs) :
  R.v39719 (state s) (inputs i) = Zmod.unsigned (N.v39719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39719 s i)) at 1.
  unfold R.v39719, N.v39719.
  rewrite ?node_39712.
  rewrite ?node_39713.
  rewrite ?node_39714.
  rewrite ?node_39718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39720 (s : N.State) (i : N.Inputs) :
  R.v39720 (state s) (inputs i) = Zmod.unsigned (N.v39720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39720 s i)) at 1.
  unfold R.v39720, N.v39720.
  unfold R.v6, N.v6.
  rewrite ?node_39719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39721 (s : N.State) (i : N.Inputs) :
  R.v39721 (state s) (inputs i) = Zmod.unsigned (N.v39721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39721 s i)) at 1.
  unfold R.v39721, N.v39721.
  rewrite ?node_7222.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39722 (s : N.State) (i : N.Inputs) :
  R.v39722 (state s) (inputs i) = Zmod.unsigned (N.v39722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39722 s i)) at 1.
  unfold R.v39722, N.v39722.
  unfold R.v6, N.v6.
  rewrite ?node_7323.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39723 (s : N.State) (i : N.Inputs) :
  R.v39723 (state s) (inputs i) = Zmod.unsigned (N.v39723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39723 s i)) at 1.
  unfold R.v39723, N.v39723.
  unfold R.v6, N.v6.
  rewrite ?node_7350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39724 (s : N.State) (i : N.Inputs) :
  R.v39724 (state s) (inputs i) = Zmod.unsigned (N.v39724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39724 s i)) at 1.
  unfold R.v39724, N.v39724.
  rewrite ?node_39721.
  rewrite ?node_39722.
  rewrite ?node_39723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39725 (s : N.State) (i : N.Inputs) :
  R.v39725 (state s) (inputs i) = Zmod.unsigned (N.v39725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39725 s i)) at 1.
  unfold R.v39725, N.v39725.
  rewrite ?node_39720.
  rewrite ?node_39724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39726 (s : N.State) (i : N.Inputs) :
  R.v39726 (state s) (inputs i) = Zmod.unsigned (N.v39726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39726 s i)) at 1.
  unfold R.v39726, N.v39726.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39727 (s : N.State) (i : N.Inputs) :
  R.v39727 (state s) (inputs i) = Zmod.unsigned (N.v39727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39727 s i)) at 1.
  unfold R.v39727, N.v39727.
  rewrite ?node_7213.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39728 (s : N.State) (i : N.Inputs) :
  R.v39728 (state s) (inputs i) = Zmod.unsigned (N.v39728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39728 s i)) at 1.
  unfold R.v39728, N.v39728.
  unfold R.v6, N.v6.
  rewrite ?node_7209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39729 (s : N.State) (i : N.Inputs) :
  R.v39729 (state s) (inputs i) = Zmod.unsigned (N.v39729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39729 s i)) at 1.
  unfold R.v39729, N.v39729.
  unfold R.v6, N.v6.
  rewrite ?node_7208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39730 (s : N.State) (i : N.Inputs) :
  R.v39730 (state s) (inputs i) = Zmod.unsigned (N.v39730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39730 s i)) at 1.
  unfold R.v39730, N.v39730.
  rewrite ?node_39728.
  rewrite ?node_39729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39731 (s : N.State) (i : N.Inputs) :
  R.v39731 (state s) (inputs i) = Zmod.unsigned (N.v39731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39731 s i)) at 1.
  unfold R.v39731, N.v39731.
  unfold R.v16484, N.v16484.
  rewrite ?node_39730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39732 (s : N.State) (i : N.Inputs) :
  R.v39732 (state s) (inputs i) = Zmod.unsigned (N.v39732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39732 s i)) at 1.
  unfold R.v39732, N.v39732.
  rewrite ?node_39727.
  rewrite ?node_39731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39733 (s : N.State) (i : N.Inputs) :
  R.v39733 (state s) (inputs i) = Zmod.unsigned (N.v39733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39733 s i)) at 1.
  unfold R.v39733, N.v39733.
  unfold R.v6, N.v6.
  rewrite ?node_39732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39734 (s : N.State) (i : N.Inputs) :
  R.v39734 (state s) (inputs i) = Zmod.unsigned (N.v39734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39734 s i)) at 1.
  unfold R.v39734, N.v39734.
  rewrite ?node_7214.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39735 (s : N.State) (i : N.Inputs) :
  R.v39735 (state s) (inputs i) = Zmod.unsigned (N.v39735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39735 s i)) at 1.
  unfold R.v39735, N.v39735.
  unfold R.v6, N.v6.
  rewrite ?node_7323.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39736 (s : N.State) (i : N.Inputs) :
  R.v39736 (state s) (inputs i) = Zmod.unsigned (N.v39736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39736 s i)) at 1.
  unfold R.v39736, N.v39736.
  rewrite ?node_39734.
  rewrite ?node_39735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39737 (s : N.State) (i : N.Inputs) :
  R.v39737 (state s) (inputs i) = Zmod.unsigned (N.v39737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39737 s i)) at 1.
  unfold R.v39737, N.v39737.
  rewrite ?node_39733.
  rewrite ?node_39736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39738 (s : N.State) (i : N.Inputs) :
  R.v39738 (state s) (inputs i) = Zmod.unsigned (N.v39738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39738 s i)) at 1.
  unfold R.v39738, N.v39738.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39739 (s : N.State) (i : N.Inputs) :
  R.v39739 (state s) (inputs i) = Zmod.unsigned (N.v39739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39739 s i)) at 1.
  unfold R.v39739, N.v39739.
  rewrite ?node_7221.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39740 (s : N.State) (i : N.Inputs) :
  R.v39740 (state s) (inputs i) = Zmod.unsigned (N.v39740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39740 s i)) at 1.
  unfold R.v39740, N.v39740.
  unfold R.v6, N.v6.
  rewrite ?node_7217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39741 (s : N.State) (i : N.Inputs) :
  R.v39741 (state s) (inputs i) = Zmod.unsigned (N.v39741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39741 s i)) at 1.
  unfold R.v39741, N.v39741.
  unfold R.v6, N.v6.
  rewrite ?node_7214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39742 (s : N.State) (i : N.Inputs) :
  R.v39742 (state s) (inputs i) = Zmod.unsigned (N.v39742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39742 s i)) at 1.
  unfold R.v39742, N.v39742.
  rewrite ?node_39740.
  rewrite ?node_39741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39743 (s : N.State) (i : N.Inputs) :
  R.v39743 (state s) (inputs i) = Zmod.unsigned (N.v39743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39743 s i)) at 1.
  unfold R.v39743, N.v39743.
  unfold R.v16484, N.v16484.
  rewrite ?node_39742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39744 (s : N.State) (i : N.Inputs) :
  R.v39744 (state s) (inputs i) = Zmod.unsigned (N.v39744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39744 s i)) at 1.
  unfold R.v39744, N.v39744.
  rewrite ?node_39739.
  rewrite ?node_39743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39745 (s : N.State) (i : N.Inputs) :
  R.v39745 (state s) (inputs i) = Zmod.unsigned (N.v39745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39745 s i)) at 1.
  unfold R.v39745, N.v39745.
  unfold R.v6, N.v6.
  rewrite ?node_39744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39746 (s : N.State) (i : N.Inputs) :
  R.v39746 (state s) (inputs i) = Zmod.unsigned (N.v39746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39746 s i)) at 1.
  unfold R.v39746, N.v39746.
  rewrite ?node_7222.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39747 (s : N.State) (i : N.Inputs) :
  R.v39747 (state s) (inputs i) = Zmod.unsigned (N.v39747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39747 s i)) at 1.
  unfold R.v39747, N.v39747.
  unfold R.v6, N.v6.
  rewrite ?node_7350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39748 (s : N.State) (i : N.Inputs) :
  R.v39748 (state s) (inputs i) = Zmod.unsigned (N.v39748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39748 s i)) at 1.
  unfold R.v39748, N.v39748.
  rewrite ?node_39746.
  rewrite ?node_39747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39749 (s : N.State) (i : N.Inputs) :
  R.v39749 (state s) (inputs i) = Zmod.unsigned (N.v39749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39749 s i)) at 1.
  unfold R.v39749, N.v39749.
  rewrite ?node_39745.
  rewrite ?node_39748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39750 (s : N.State) (i : N.Inputs) :
  R.v39750 (state s) (inputs i) = Zmod.unsigned (N.v39750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39750 s i)) at 1.
  unfold R.v39750, N.v39750.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39751 (s : N.State) (i : N.Inputs) :
  R.v39751 (state s) (inputs i) = Zmod.unsigned (N.v39751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39751 s i)) at 1.
  unfold R.v39751, N.v39751.
  rewrite ?node_7233.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39752 (s : N.State) (i : N.Inputs) :
  R.v39752 (state s) (inputs i) = Zmod.unsigned (N.v39752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39752 s i)) at 1.
  unfold R.v39752, N.v39752.
  unfold R.v6, N.v6.
  rewrite ?node_7229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39753 (s : N.State) (i : N.Inputs) :
  R.v39753 (state s) (inputs i) = Zmod.unsigned (N.v39753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39753 s i)) at 1.
  unfold R.v39753, N.v39753.
  unfold R.v6, N.v6.
  rewrite ?node_7226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39754 (s : N.State) (i : N.Inputs) :
  R.v39754 (state s) (inputs i) = Zmod.unsigned (N.v39754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39754 s i)) at 1.
  unfold R.v39754, N.v39754.
  rewrite ?node_39752.
  rewrite ?node_39753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39755 (s : N.State) (i : N.Inputs) :
  R.v39755 (state s) (inputs i) = Zmod.unsigned (N.v39755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39755 s i)) at 1.
  unfold R.v39755, N.v39755.
  unfold R.v16484, N.v16484.
  rewrite ?node_39754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39756 (s : N.State) (i : N.Inputs) :
  R.v39756 (state s) (inputs i) = Zmod.unsigned (N.v39756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39756 s i)) at 1.
  unfold R.v39756, N.v39756.
  rewrite ?node_39751.
  rewrite ?node_39755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39757 (s : N.State) (i : N.Inputs) :
  R.v39757 (state s) (inputs i) = Zmod.unsigned (N.v39757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39757 s i)) at 1.
  unfold R.v39757, N.v39757.
  unfold R.v6, N.v6.
  rewrite ?node_39756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39758 (s : N.State) (i : N.Inputs) :
  R.v39758 (state s) (inputs i) = Zmod.unsigned (N.v39758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39758 s i)) at 1.
  unfold R.v39758, N.v39758.
  rewrite ?node_7234.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39759 (s : N.State) (i : N.Inputs) :
  R.v39759 (state s) (inputs i) = Zmod.unsigned (N.v39759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39759 s i)) at 1.
  unfold R.v39759, N.v39759.
  unfold R.v6, N.v6.
  rewrite ?node_7353.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39760 (s : N.State) (i : N.Inputs) :
  R.v39760 (state s) (inputs i) = Zmod.unsigned (N.v39760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39760 s i)) at 1.
  unfold R.v39760, N.v39760.
  rewrite ?node_39758.
  rewrite ?node_39759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39761 (s : N.State) (i : N.Inputs) :
  R.v39761 (state s) (inputs i) = Zmod.unsigned (N.v39761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39761 s i)) at 1.
  unfold R.v39761, N.v39761.
  rewrite ?node_39757.
  rewrite ?node_39760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39762 (s : N.State) (i : N.Inputs) :
  R.v39762 (state s) (inputs i) = Zmod.unsigned (N.v39762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39762 s i)) at 1.
  unfold R.v39762, N.v39762.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39763 (s : N.State) (i : N.Inputs) :
  R.v39763 (state s) (inputs i) = Zmod.unsigned (N.v39763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39763 s i)) at 1.
  unfold R.v39763, N.v39763.
  rewrite ?node_7302.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39764 (s : N.State) (i : N.Inputs) :
  R.v39764 (state s) (inputs i) = Zmod.unsigned (N.v39764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39764 s i)) at 1.
  unfold R.v39764, N.v39764.
  rewrite ?node_7298.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39765 (s : N.State) (i : N.Inputs) :
  R.v39765 (state s) (inputs i) = Zmod.unsigned (N.v39765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39765 s i)) at 1.
  unfold R.v39765, N.v39765.
  rewrite ?node_7290.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39766 (s : N.State) (i : N.Inputs) :
  R.v39766 (state s) (inputs i) = Zmod.unsigned (N.v39766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39766 s i)) at 1.
  unfold R.v39766, N.v39766.
  unfold R.v6, N.v6.
  rewrite ?node_7282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39767 (s : N.State) (i : N.Inputs) :
  R.v39767 (state s) (inputs i) = Zmod.unsigned (N.v39767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39767 s i)) at 1.
  unfold R.v39767, N.v39767.
  unfold R.v6, N.v6.
  rewrite ?node_7275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39768 (s : N.State) (i : N.Inputs) :
  R.v39768 (state s) (inputs i) = Zmod.unsigned (N.v39768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39768 s i)) at 1.
  unfold R.v39768, N.v39768.
  rewrite ?node_39766.
  rewrite ?node_39767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39769 (s : N.State) (i : N.Inputs) :
  R.v39769 (state s) (inputs i) = Zmod.unsigned (N.v39769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39769 s i)) at 1.
  unfold R.v39769, N.v39769.
  unfold R.v16484, N.v16484.
  rewrite ?node_39768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39770 (s : N.State) (i : N.Inputs) :
  R.v39770 (state s) (inputs i) = Zmod.unsigned (N.v39770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39770 s i)) at 1.
  unfold R.v39770, N.v39770.
  rewrite ?node_39763.
  rewrite ?node_39764.
  rewrite ?node_39765.
  rewrite ?node_39769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39771 (s : N.State) (i : N.Inputs) :
  R.v39771 (state s) (inputs i) = Zmod.unsigned (N.v39771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39771 s i)) at 1.
  unfold R.v39771, N.v39771.
  unfold R.v6, N.v6.
  rewrite ?node_39770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39772 (s : N.State) (i : N.Inputs) :
  R.v39772 (state s) (inputs i) = Zmod.unsigned (N.v39772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39772 s i)) at 1.
  unfold R.v39772, N.v39772.
  rewrite ?node_7303.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39773 (s : N.State) (i : N.Inputs) :
  R.v39773 (state s) (inputs i) = Zmod.unsigned (N.v39773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39773 s i)) at 1.
  unfold R.v39773, N.v39773.
  unfold R.v6, N.v6.
  rewrite ?node_7406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39774 (s : N.State) (i : N.Inputs) :
  R.v39774 (state s) (inputs i) = Zmod.unsigned (N.v39774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39774 s i)) at 1.
  unfold R.v39774, N.v39774.
  unfold R.v6, N.v6.
  rewrite ?node_7451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39775 (s : N.State) (i : N.Inputs) :
  R.v39775 (state s) (inputs i) = Zmod.unsigned (N.v39775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39775 s i)) at 1.
  unfold R.v39775, N.v39775.
  rewrite ?node_39772.
  rewrite ?node_39773.
  rewrite ?node_39774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39776 (s : N.State) (i : N.Inputs) :
  R.v39776 (state s) (inputs i) = Zmod.unsigned (N.v39776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39776 s i)) at 1.
  unfold R.v39776, N.v39776.
  rewrite ?node_39771.
  rewrite ?node_39775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39777 (s : N.State) (i : N.Inputs) :
  R.v39777 (state s) (inputs i) = Zmod.unsigned (N.v39777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39777 s i)) at 1.
  unfold R.v39777, N.v39777.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39778 (s : N.State) (i : N.Inputs) :
  R.v39778 (state s) (inputs i) = Zmod.unsigned (N.v39778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39778 s i)) at 1.
  unfold R.v39778, N.v39778.
  rewrite ?node_7290.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39779 (s : N.State) (i : N.Inputs) :
  R.v39779 (state s) (inputs i) = Zmod.unsigned (N.v39779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39779 s i)) at 1.
  unfold R.v39779, N.v39779.
  unfold R.v6, N.v6.
  rewrite ?node_7282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39780 (s : N.State) (i : N.Inputs) :
  R.v39780 (state s) (inputs i) = Zmod.unsigned (N.v39780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39780 s i)) at 1.
  unfold R.v39780, N.v39780.
  unfold R.v6, N.v6.
  rewrite ?node_7275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39781 (s : N.State) (i : N.Inputs) :
  R.v39781 (state s) (inputs i) = Zmod.unsigned (N.v39781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39781 s i)) at 1.
  unfold R.v39781, N.v39781.
  rewrite ?node_39779.
  rewrite ?node_39780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39782 (s : N.State) (i : N.Inputs) :
  R.v39782 (state s) (inputs i) = Zmod.unsigned (N.v39782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39782 s i)) at 1.
  unfold R.v39782, N.v39782.
  unfold R.v16484, N.v16484.
  rewrite ?node_39781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39783 (s : N.State) (i : N.Inputs) :
  R.v39783 (state s) (inputs i) = Zmod.unsigned (N.v39783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39783 s i)) at 1.
  unfold R.v39783, N.v39783.
  rewrite ?node_39778.
  rewrite ?node_39782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39784 (s : N.State) (i : N.Inputs) :
  R.v39784 (state s) (inputs i) = Zmod.unsigned (N.v39784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39784 s i)) at 1.
  unfold R.v39784, N.v39784.
  unfold R.v6, N.v6.
  rewrite ?node_39783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39785 (s : N.State) (i : N.Inputs) :
  R.v39785 (state s) (inputs i) = Zmod.unsigned (N.v39785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39785 s i)) at 1.
  unfold R.v39785, N.v39785.
  rewrite ?node_7291.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39786 (s : N.State) (i : N.Inputs) :
  R.v39786 (state s) (inputs i) = Zmod.unsigned (N.v39786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39786 s i)) at 1.
  unfold R.v39786, N.v39786.
  unfold R.v6, N.v6.
  rewrite ?node_7406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39787 (s : N.State) (i : N.Inputs) :
  R.v39787 (state s) (inputs i) = Zmod.unsigned (N.v39787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39787 s i)) at 1.
  unfold R.v39787, N.v39787.
  rewrite ?node_39785.
  rewrite ?node_39786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39788 (s : N.State) (i : N.Inputs) :
  R.v39788 (state s) (inputs i) = Zmod.unsigned (N.v39788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39788 s i)) at 1.
  unfold R.v39788, N.v39788.
  rewrite ?node_39784.
  rewrite ?node_39787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39789 (s : N.State) (i : N.Inputs) :
  R.v39789 (state s) (inputs i) = Zmod.unsigned (N.v39789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39789 s i)) at 1.
  unfold R.v39789, N.v39789.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39790 (s : N.State) (i : N.Inputs) :
  R.v39790 (state s) (inputs i) = Zmod.unsigned (N.v39790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39790 s i)) at 1.
  unfold R.v39790, N.v39790.
  rewrite ?node_7302.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39791 (s : N.State) (i : N.Inputs) :
  R.v39791 (state s) (inputs i) = Zmod.unsigned (N.v39791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39791 s i)) at 1.
  unfold R.v39791, N.v39791.
  unfold R.v6, N.v6.
  rewrite ?node_7298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39792 (s : N.State) (i : N.Inputs) :
  R.v39792 (state s) (inputs i) = Zmod.unsigned (N.v39792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39792 s i)) at 1.
  unfold R.v39792, N.v39792.
  unfold R.v6, N.v6.
  rewrite ?node_7291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39793 (s : N.State) (i : N.Inputs) :
  R.v39793 (state s) (inputs i) = Zmod.unsigned (N.v39793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39793 s i)) at 1.
  unfold R.v39793, N.v39793.
  rewrite ?node_39791.
  rewrite ?node_39792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39794 (s : N.State) (i : N.Inputs) :
  R.v39794 (state s) (inputs i) = Zmod.unsigned (N.v39794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39794 s i)) at 1.
  unfold R.v39794, N.v39794.
  unfold R.v16484, N.v16484.
  rewrite ?node_39793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39795 (s : N.State) (i : N.Inputs) :
  R.v39795 (state s) (inputs i) = Zmod.unsigned (N.v39795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39795 s i)) at 1.
  unfold R.v39795, N.v39795.
  rewrite ?node_39790.
  rewrite ?node_39794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39796 (s : N.State) (i : N.Inputs) :
  R.v39796 (state s) (inputs i) = Zmod.unsigned (N.v39796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39796 s i)) at 1.
  unfold R.v39796, N.v39796.
  unfold R.v6, N.v6.
  rewrite ?node_39795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39797 (s : N.State) (i : N.Inputs) :
  R.v39797 (state s) (inputs i) = Zmod.unsigned (N.v39797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39797 s i)) at 1.
  unfold R.v39797, N.v39797.
  rewrite ?node_7303.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39798 (s : N.State) (i : N.Inputs) :
  R.v39798 (state s) (inputs i) = Zmod.unsigned (N.v39798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39798 s i)) at 1.
  unfold R.v39798, N.v39798.
  unfold R.v6, N.v6.
  rewrite ?node_7451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39799 (s : N.State) (i : N.Inputs) :
  R.v39799 (state s) (inputs i) = Zmod.unsigned (N.v39799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39799 s i)) at 1.
  unfold R.v39799, N.v39799.
  rewrite ?node_39797.
  rewrite ?node_39798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39800 (s : N.State) (i : N.Inputs) :
  R.v39800 (state s) (inputs i) = Zmod.unsigned (N.v39800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39800 s i)) at 1.
  unfold R.v39800, N.v39800.
  rewrite ?node_39796.
  rewrite ?node_39799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39801 (s : N.State) (i : N.Inputs) :
  R.v39801 (state s) (inputs i) = Zmod.unsigned (N.v39801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39801 s i)) at 1.
  unfold R.v39801, N.v39801.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39802 (s : N.State) (i : N.Inputs) :
  R.v39802 (state s) (inputs i) = Zmod.unsigned (N.v39802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39802 s i)) at 1.
  unfold R.v39802, N.v39802.
  rewrite ?node_7323.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39803 (s : N.State) (i : N.Inputs) :
  R.v39803 (state s) (inputs i) = Zmod.unsigned (N.v39803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39803 s i)) at 1.
  unfold R.v39803, N.v39803.
  rewrite ?node_7319.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39804 (s : N.State) (i : N.Inputs) :
  R.v39804 (state s) (inputs i) = Zmod.unsigned (N.v39804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39804 s i)) at 1.
  unfold R.v39804, N.v39804.
  rewrite ?node_7315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39805 (s : N.State) (i : N.Inputs) :
  R.v39805 (state s) (inputs i) = Zmod.unsigned (N.v39805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39805 s i)) at 1.
  unfold R.v39805, N.v39805.
  unfold R.v6, N.v6.
  rewrite ?node_7311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39806 (s : N.State) (i : N.Inputs) :
  R.v39806 (state s) (inputs i) = Zmod.unsigned (N.v39806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39806 s i)) at 1.
  unfold R.v39806, N.v39806.
  unfold R.v6, N.v6.
  rewrite ?node_7310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39807 (s : N.State) (i : N.Inputs) :
  R.v39807 (state s) (inputs i) = Zmod.unsigned (N.v39807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39807 s i)) at 1.
  unfold R.v39807, N.v39807.
  rewrite ?node_39805.
  rewrite ?node_39806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39808 (s : N.State) (i : N.Inputs) :
  R.v39808 (state s) (inputs i) = Zmod.unsigned (N.v39808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39808 s i)) at 1.
  unfold R.v39808, N.v39808.
  unfold R.v16484, N.v16484.
  rewrite ?node_39807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39809 (s : N.State) (i : N.Inputs) :
  R.v39809 (state s) (inputs i) = Zmod.unsigned (N.v39809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39809 s i)) at 1.
  unfold R.v39809, N.v39809.
  rewrite ?node_39802.
  rewrite ?node_39803.
  rewrite ?node_39804.
  rewrite ?node_39808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39810 (s : N.State) (i : N.Inputs) :
  R.v39810 (state s) (inputs i) = Zmod.unsigned (N.v39810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39810 s i)) at 1.
  unfold R.v39810, N.v39810.
  unfold R.v6, N.v6.
  rewrite ?node_39809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39811 (s : N.State) (i : N.Inputs) :
  R.v39811 (state s) (inputs i) = Zmod.unsigned (N.v39811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39811 s i)) at 1.
  unfold R.v39811, N.v39811.
  rewrite ?node_7324.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39812 (s : N.State) (i : N.Inputs) :
  R.v39812 (state s) (inputs i) = Zmod.unsigned (N.v39812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39812 s i)) at 1.
  unfold R.v39812, N.v39812.
  unfold R.v6, N.v6.
  rewrite ?node_7428.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39813 (s : N.State) (i : N.Inputs) :
  R.v39813 (state s) (inputs i) = Zmod.unsigned (N.v39813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39813 s i)) at 1.
  unfold R.v39813, N.v39813.
  unfold R.v6, N.v6.
  rewrite ?node_7459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39814 (s : N.State) (i : N.Inputs) :
  R.v39814 (state s) (inputs i) = Zmod.unsigned (N.v39814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39814 s i)) at 1.
  unfold R.v39814, N.v39814.
  rewrite ?node_39811.
  rewrite ?node_39812.
  rewrite ?node_39813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39815 (s : N.State) (i : N.Inputs) :
  R.v39815 (state s) (inputs i) = Zmod.unsigned (N.v39815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39815 s i)) at 1.
  unfold R.v39815, N.v39815.
  rewrite ?node_39810.
  rewrite ?node_39814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39816 (s : N.State) (i : N.Inputs) :
  R.v39816 (state s) (inputs i) = Zmod.unsigned (N.v39816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39816 s i)) at 1.
  unfold R.v39816, N.v39816.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39817 (s : N.State) (i : N.Inputs) :
  R.v39817 (state s) (inputs i) = Zmod.unsigned (N.v39817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39817 s i)) at 1.
  unfold R.v39817, N.v39817.
  rewrite ?node_7315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39818 (s : N.State) (i : N.Inputs) :
  R.v39818 (state s) (inputs i) = Zmod.unsigned (N.v39818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39818 s i)) at 1.
  unfold R.v39818, N.v39818.
  unfold R.v6, N.v6.
  rewrite ?node_7311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39819 (s : N.State) (i : N.Inputs) :
  R.v39819 (state s) (inputs i) = Zmod.unsigned (N.v39819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39819 s i)) at 1.
  unfold R.v39819, N.v39819.
  unfold R.v6, N.v6.
  rewrite ?node_7310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39820 (s : N.State) (i : N.Inputs) :
  R.v39820 (state s) (inputs i) = Zmod.unsigned (N.v39820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39820 s i)) at 1.
  unfold R.v39820, N.v39820.
  rewrite ?node_39818.
  rewrite ?node_39819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39821 (s : N.State) (i : N.Inputs) :
  R.v39821 (state s) (inputs i) = Zmod.unsigned (N.v39821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39821 s i)) at 1.
  unfold R.v39821, N.v39821.
  unfold R.v16484, N.v16484.
  rewrite ?node_39820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39822 (s : N.State) (i : N.Inputs) :
  R.v39822 (state s) (inputs i) = Zmod.unsigned (N.v39822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39822 s i)) at 1.
  unfold R.v39822, N.v39822.
  rewrite ?node_39817.
  rewrite ?node_39821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39823 (s : N.State) (i : N.Inputs) :
  R.v39823 (state s) (inputs i) = Zmod.unsigned (N.v39823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39823 s i)) at 1.
  unfold R.v39823, N.v39823.
  unfold R.v6, N.v6.
  rewrite ?node_39822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39824 (s : N.State) (i : N.Inputs) :
  R.v39824 (state s) (inputs i) = Zmod.unsigned (N.v39824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39824 s i)) at 1.
  unfold R.v39824, N.v39824.
  rewrite ?node_7316.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39825 (s : N.State) (i : N.Inputs) :
  R.v39825 (state s) (inputs i) = Zmod.unsigned (N.v39825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39825 s i)) at 1.
  unfold R.v39825, N.v39825.
  unfold R.v6, N.v6.
  rewrite ?node_7428.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39826 (s : N.State) (i : N.Inputs) :
  R.v39826 (state s) (inputs i) = Zmod.unsigned (N.v39826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39826 s i)) at 1.
  unfold R.v39826, N.v39826.
  rewrite ?node_39824.
  rewrite ?node_39825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39827 (s : N.State) (i : N.Inputs) :
  R.v39827 (state s) (inputs i) = Zmod.unsigned (N.v39827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39827 s i)) at 1.
  unfold R.v39827, N.v39827.
  rewrite ?node_39823.
  rewrite ?node_39826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39828 (s : N.State) (i : N.Inputs) :
  R.v39828 (state s) (inputs i) = Zmod.unsigned (N.v39828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39828 s i)) at 1.
  unfold R.v39828, N.v39828.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39829 (s : N.State) (i : N.Inputs) :
  R.v39829 (state s) (inputs i) = Zmod.unsigned (N.v39829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39829 s i)) at 1.
  unfold R.v39829, N.v39829.
  rewrite ?node_7323.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39830 (s : N.State) (i : N.Inputs) :
  R.v39830 (state s) (inputs i) = Zmod.unsigned (N.v39830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39830 s i)) at 1.
  unfold R.v39830, N.v39830.
  unfold R.v6, N.v6.
  rewrite ?node_7319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39831 (s : N.State) (i : N.Inputs) :
  R.v39831 (state s) (inputs i) = Zmod.unsigned (N.v39831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39831 s i)) at 1.
  unfold R.v39831, N.v39831.
  unfold R.v6, N.v6.
  rewrite ?node_7316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39832 (s : N.State) (i : N.Inputs) :
  R.v39832 (state s) (inputs i) = Zmod.unsigned (N.v39832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39832 s i)) at 1.
  unfold R.v39832, N.v39832.
  rewrite ?node_39830.
  rewrite ?node_39831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39833 (s : N.State) (i : N.Inputs) :
  R.v39833 (state s) (inputs i) = Zmod.unsigned (N.v39833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39833 s i)) at 1.
  unfold R.v39833, N.v39833.
  unfold R.v16484, N.v16484.
  rewrite ?node_39832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39834 (s : N.State) (i : N.Inputs) :
  R.v39834 (state s) (inputs i) = Zmod.unsigned (N.v39834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39834 s i)) at 1.
  unfold R.v39834, N.v39834.
  rewrite ?node_39829.
  rewrite ?node_39833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39835 (s : N.State) (i : N.Inputs) :
  R.v39835 (state s) (inputs i) = Zmod.unsigned (N.v39835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39835 s i)) at 1.
  unfold R.v39835, N.v39835.
  unfold R.v6, N.v6.
  rewrite ?node_39834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39836 (s : N.State) (i : N.Inputs) :
  R.v39836 (state s) (inputs i) = Zmod.unsigned (N.v39836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39836 s i)) at 1.
  unfold R.v39836, N.v39836.
  rewrite ?node_7324.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39837 (s : N.State) (i : N.Inputs) :
  R.v39837 (state s) (inputs i) = Zmod.unsigned (N.v39837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39837 s i)) at 1.
  unfold R.v39837, N.v39837.
  unfold R.v6, N.v6.
  rewrite ?node_7459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39838 (s : N.State) (i : N.Inputs) :
  R.v39838 (state s) (inputs i) = Zmod.unsigned (N.v39838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39838 s i)) at 1.
  unfold R.v39838, N.v39838.
  rewrite ?node_39836.
  rewrite ?node_39837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39839 (s : N.State) (i : N.Inputs) :
  R.v39839 (state s) (inputs i) = Zmod.unsigned (N.v39839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39839 s i)) at 1.
  unfold R.v39839, N.v39839.
  rewrite ?node_39835.
  rewrite ?node_39838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39840 (s : N.State) (i : N.Inputs) :
  R.v39840 (state s) (inputs i) = Zmod.unsigned (N.v39840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39840 s i)) at 1.
  unfold R.v39840, N.v39840.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39841 (s : N.State) (i : N.Inputs) :
  R.v39841 (state s) (inputs i) = Zmod.unsigned (N.v39841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39841 s i)) at 1.
  unfold R.v39841, N.v39841.
  rewrite ?node_7337.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39842 (s : N.State) (i : N.Inputs) :
  R.v39842 (state s) (inputs i) = Zmod.unsigned (N.v39842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39842 s i)) at 1.
  unfold R.v39842, N.v39842.
  rewrite ?node_7335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39843 (s : N.State) (i : N.Inputs) :
  R.v39843 (state s) (inputs i) = Zmod.unsigned (N.v39843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39843 s i)) at 1.
  unfold R.v39843, N.v39843.
  unfold R.v6, N.v6.
  rewrite ?node_7331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39844 (s : N.State) (i : N.Inputs) :
  R.v39844 (state s) (inputs i) = Zmod.unsigned (N.v39844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39844 s i)) at 1.
  unfold R.v39844, N.v39844.
  unfold R.v6, N.v6.
  rewrite ?node_7328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39845 (s : N.State) (i : N.Inputs) :
  R.v39845 (state s) (inputs i) = Zmod.unsigned (N.v39845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39845 s i)) at 1.
  unfold R.v39845, N.v39845.
  rewrite ?node_39843.
  rewrite ?node_39844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39846 (s : N.State) (i : N.Inputs) :
  R.v39846 (state s) (inputs i) = Zmod.unsigned (N.v39846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39846 s i)) at 1.
  unfold R.v39846, N.v39846.
  unfold R.v16484, N.v16484.
  rewrite ?node_39845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39847 (s : N.State) (i : N.Inputs) :
  R.v39847 (state s) (inputs i) = Zmod.unsigned (N.v39847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39847 s i)) at 1.
  unfold R.v39847, N.v39847.
  rewrite ?node_39841.
  rewrite ?node_39842.
  rewrite ?node_39846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39848 (s : N.State) (i : N.Inputs) :
  R.v39848 (state s) (inputs i) = Zmod.unsigned (N.v39848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39848 s i)) at 1.
  unfold R.v39848, N.v39848.
  unfold R.v6, N.v6.
  rewrite ?node_39847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39849 (s : N.State) (i : N.Inputs) :
  R.v39849 (state s) (inputs i) = Zmod.unsigned (N.v39849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39849 s i)) at 1.
  unfold R.v39849, N.v39849.
  rewrite ?node_7338.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39850 (s : N.State) (i : N.Inputs) :
  R.v39850 (state s) (inputs i) = Zmod.unsigned (N.v39850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39850 s i)) at 1.
  unfold R.v39850, N.v39850.
  unfold R.v6, N.v6.
  rewrite ?node_7446.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39851 (s : N.State) (i : N.Inputs) :
  R.v39851 (state s) (inputs i) = Zmod.unsigned (N.v39851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39851 s i)) at 1.
  unfold R.v39851, N.v39851.
  unfold R.v6, N.v6.
  rewrite ?node_7460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39852 (s : N.State) (i : N.Inputs) :
  R.v39852 (state s) (inputs i) = Zmod.unsigned (N.v39852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39852 s i)) at 1.
  unfold R.v39852, N.v39852.
  rewrite ?node_39849.
  rewrite ?node_39850.
  rewrite ?node_39851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39853 (s : N.State) (i : N.Inputs) :
  R.v39853 (state s) (inputs i) = Zmod.unsigned (N.v39853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39853 s i)) at 1.
  unfold R.v39853, N.v39853.
  rewrite ?node_39848.
  rewrite ?node_39852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39854 (s : N.State) (i : N.Inputs) :
  R.v39854 (state s) (inputs i) = Zmod.unsigned (N.v39854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39854 s i)) at 1.
  unfold R.v39854, N.v39854.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39855 (s : N.State) (i : N.Inputs) :
  R.v39855 (state s) (inputs i) = Zmod.unsigned (N.v39855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39855 s i)) at 1.
  unfold R.v39855, N.v39855.
  rewrite ?node_7335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39856 (s : N.State) (i : N.Inputs) :
  R.v39856 (state s) (inputs i) = Zmod.unsigned (N.v39856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39856 s i)) at 1.
  unfold R.v39856, N.v39856.
  unfold R.v6, N.v6.
  rewrite ?node_7331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39857 (s : N.State) (i : N.Inputs) :
  R.v39857 (state s) (inputs i) = Zmod.unsigned (N.v39857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39857 s i)) at 1.
  unfold R.v39857, N.v39857.
  unfold R.v6, N.v6.
  rewrite ?node_7328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39858 (s : N.State) (i : N.Inputs) :
  R.v39858 (state s) (inputs i) = Zmod.unsigned (N.v39858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39858 s i)) at 1.
  unfold R.v39858, N.v39858.
  rewrite ?node_39856.
  rewrite ?node_39857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39859 (s : N.State) (i : N.Inputs) :
  R.v39859 (state s) (inputs i) = Zmod.unsigned (N.v39859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39859 s i)) at 1.
  unfold R.v39859, N.v39859.
  unfold R.v16484, N.v16484.
  rewrite ?node_39858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39860 (s : N.State) (i : N.Inputs) :
  R.v39860 (state s) (inputs i) = Zmod.unsigned (N.v39860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39860 s i)) at 1.
  unfold R.v39860, N.v39860.
  rewrite ?node_39855.
  rewrite ?node_39859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39861 (s : N.State) (i : N.Inputs) :
  R.v39861 (state s) (inputs i) = Zmod.unsigned (N.v39861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39861 s i)) at 1.
  unfold R.v39861, N.v39861.
  unfold R.v6, N.v6.
  rewrite ?node_39860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39862 (s : N.State) (i : N.Inputs) :
  R.v39862 (state s) (inputs i) = Zmod.unsigned (N.v39862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39862 s i)) at 1.
  unfold R.v39862, N.v39862.
  rewrite ?node_7336.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39863 (s : N.State) (i : N.Inputs) :
  R.v39863 (state s) (inputs i) = Zmod.unsigned (N.v39863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39863 s i)) at 1.
  unfold R.v39863, N.v39863.
  unfold R.v6, N.v6.
  rewrite ?node_7446.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39864 (s : N.State) (i : N.Inputs) :
  R.v39864 (state s) (inputs i) = Zmod.unsigned (N.v39864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39864 s i)) at 1.
  unfold R.v39864, N.v39864.
  rewrite ?node_39862.
  rewrite ?node_39863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39865 (s : N.State) (i : N.Inputs) :
  R.v39865 (state s) (inputs i) = Zmod.unsigned (N.v39865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39865 s i)) at 1.
  unfold R.v39865, N.v39865.
  rewrite ?node_39861.
  rewrite ?node_39864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39866 (s : N.State) (i : N.Inputs) :
  R.v39866 (state s) (inputs i) = Zmod.unsigned (N.v39866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39866 s i)) at 1.
  unfold R.v39866, N.v39866.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39867 (s : N.State) (i : N.Inputs) :
  R.v39867 (state s) (inputs i) = Zmod.unsigned (N.v39867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39867 s i)) at 1.
  unfold R.v39867, N.v39867.
  unfold R.v6, N.v6.
  rewrite ?node_7337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39868 (s : N.State) (i : N.Inputs) :
  R.v39868 (state s) (inputs i) = Zmod.unsigned (N.v39868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39868 s i)) at 1.
  unfold R.v39868, N.v39868.
  unfold R.v6, N.v6.
  rewrite ?node_7336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39869 (s : N.State) (i : N.Inputs) :
  R.v39869 (state s) (inputs i) = Zmod.unsigned (N.v39869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39869 s i)) at 1.
  unfold R.v39869, N.v39869.
  rewrite ?node_39867.
  rewrite ?node_39868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39870 (s : N.State) (i : N.Inputs) :
  R.v39870 (state s) (inputs i) = Zmod.unsigned (N.v39870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39870 s i)) at 1.
  unfold R.v39870, N.v39870.
  unfold R.v16463, N.v16463.
  rewrite ?node_39869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39871 (s : N.State) (i : N.Inputs) :
  R.v39871 (state s) (inputs i) = Zmod.unsigned (N.v39871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39871 s i)) at 1.
  unfold R.v39871, N.v39871.
  rewrite ?node_7338.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39872 (s : N.State) (i : N.Inputs) :
  R.v39872 (state s) (inputs i) = Zmod.unsigned (N.v39872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39872 s i)) at 1.
  unfold R.v39872, N.v39872.
  unfold R.v6, N.v6.
  rewrite ?node_7460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39873 (s : N.State) (i : N.Inputs) :
  R.v39873 (state s) (inputs i) = Zmod.unsigned (N.v39873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39873 s i)) at 1.
  unfold R.v39873, N.v39873.
  rewrite ?node_39871.
  rewrite ?node_39872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39874 (s : N.State) (i : N.Inputs) :
  R.v39874 (state s) (inputs i) = Zmod.unsigned (N.v39874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39874 s i)) at 1.
  unfold R.v39874, N.v39874.
  rewrite ?node_39870.
  rewrite ?node_39873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39875 (s : N.State) (i : N.Inputs) :
  R.v39875 (state s) (inputs i) = Zmod.unsigned (N.v39875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39875 s i)) at 1.
  unfold R.v39875, N.v39875.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39876 (s : N.State) (i : N.Inputs) :
  R.v39876 (state s) (inputs i) = Zmod.unsigned (N.v39876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39876 s i)) at 1.
  unfold R.v39876, N.v39876.
  rewrite ?node_7406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39877 (s : N.State) (i : N.Inputs) :
  R.v39877 (state s) (inputs i) = Zmod.unsigned (N.v39877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39877 s i)) at 1.
  unfold R.v39877, N.v39877.
  rewrite ?node_7402.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39878 (s : N.State) (i : N.Inputs) :
  R.v39878 (state s) (inputs i) = Zmod.unsigned (N.v39878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39878 s i)) at 1.
  unfold R.v39878, N.v39878.
  rewrite ?node_7394.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39879 (s : N.State) (i : N.Inputs) :
  R.v39879 (state s) (inputs i) = Zmod.unsigned (N.v39879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39879 s i)) at 1.
  unfold R.v39879, N.v39879.
  unfold R.v6, N.v6.
  rewrite ?node_7386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39880 (s : N.State) (i : N.Inputs) :
  R.v39880 (state s) (inputs i) = Zmod.unsigned (N.v39880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39880 s i)) at 1.
  unfold R.v39880, N.v39880.
  unfold R.v6, N.v6.
  rewrite ?node_7379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39881 (s : N.State) (i : N.Inputs) :
  R.v39881 (state s) (inputs i) = Zmod.unsigned (N.v39881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39881 s i)) at 1.
  unfold R.v39881, N.v39881.
  rewrite ?node_39879.
  rewrite ?node_39880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39882 (s : N.State) (i : N.Inputs) :
  R.v39882 (state s) (inputs i) = Zmod.unsigned (N.v39882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39882 s i)) at 1.
  unfold R.v39882, N.v39882.
  unfold R.v16484, N.v16484.
  rewrite ?node_39881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39883 (s : N.State) (i : N.Inputs) :
  R.v39883 (state s) (inputs i) = Zmod.unsigned (N.v39883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39883 s i)) at 1.
  unfold R.v39883, N.v39883.
  rewrite ?node_39876.
  rewrite ?node_39877.
  rewrite ?node_39878.
  rewrite ?node_39882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39884 (s : N.State) (i : N.Inputs) :
  R.v39884 (state s) (inputs i) = Zmod.unsigned (N.v39884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39884 s i)) at 1.
  unfold R.v39884, N.v39884.
  unfold R.v6, N.v6.
  rewrite ?node_39883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39885 (s : N.State) (i : N.Inputs) :
  R.v39885 (state s) (inputs i) = Zmod.unsigned (N.v39885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39885 s i)) at 1.
  unfold R.v39885, N.v39885.
  rewrite ?node_7407.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39886 (s : N.State) (i : N.Inputs) :
  R.v39886 (state s) (inputs i) = Zmod.unsigned (N.v39886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39886 s i)) at 1.
  unfold R.v39886, N.v39886.
  unfold R.v6, N.v6.
  rewrite ?node_7513.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39887 (s : N.State) (i : N.Inputs) :
  R.v39887 (state s) (inputs i) = Zmod.unsigned (N.v39887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39887 s i)) at 1.
  unfold R.v39887, N.v39887.
  unfold R.v6, N.v6.
  rewrite ?node_7560.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39888 (s : N.State) (i : N.Inputs) :
  R.v39888 (state s) (inputs i) = Zmod.unsigned (N.v39888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39888 s i)) at 1.
  unfold R.v39888, N.v39888.
  rewrite ?node_39885.
  rewrite ?node_39886.
  rewrite ?node_39887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39889 (s : N.State) (i : N.Inputs) :
  R.v39889 (state s) (inputs i) = Zmod.unsigned (N.v39889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39889 s i)) at 1.
  unfold R.v39889, N.v39889.
  rewrite ?node_39884.
  rewrite ?node_39888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39890 (s : N.State) (i : N.Inputs) :
  R.v39890 (state s) (inputs i) = Zmod.unsigned (N.v39890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39890 s i)) at 1.
  unfold R.v39890, N.v39890.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39891 (s : N.State) (i : N.Inputs) :
  R.v39891 (state s) (inputs i) = Zmod.unsigned (N.v39891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39891 s i)) at 1.
  unfold R.v39891, N.v39891.
  rewrite ?node_7394.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39892 (s : N.State) (i : N.Inputs) :
  R.v39892 (state s) (inputs i) = Zmod.unsigned (N.v39892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39892 s i)) at 1.
  unfold R.v39892, N.v39892.
  unfold R.v6, N.v6.
  rewrite ?node_7386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39893 (s : N.State) (i : N.Inputs) :
  R.v39893 (state s) (inputs i) = Zmod.unsigned (N.v39893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39893 s i)) at 1.
  unfold R.v39893, N.v39893.
  unfold R.v6, N.v6.
  rewrite ?node_7379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39894 (s : N.State) (i : N.Inputs) :
  R.v39894 (state s) (inputs i) = Zmod.unsigned (N.v39894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39894 s i)) at 1.
  unfold R.v39894, N.v39894.
  rewrite ?node_39892.
  rewrite ?node_39893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39895 (s : N.State) (i : N.Inputs) :
  R.v39895 (state s) (inputs i) = Zmod.unsigned (N.v39895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39895 s i)) at 1.
  unfold R.v39895, N.v39895.
  unfold R.v16484, N.v16484.
  rewrite ?node_39894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39896 (s : N.State) (i : N.Inputs) :
  R.v39896 (state s) (inputs i) = Zmod.unsigned (N.v39896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39896 s i)) at 1.
  unfold R.v39896, N.v39896.
  rewrite ?node_39891.
  rewrite ?node_39895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39897 (s : N.State) (i : N.Inputs) :
  R.v39897 (state s) (inputs i) = Zmod.unsigned (N.v39897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39897 s i)) at 1.
  unfold R.v39897, N.v39897.
  unfold R.v6, N.v6.
  rewrite ?node_39896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39898 (s : N.State) (i : N.Inputs) :
  R.v39898 (state s) (inputs i) = Zmod.unsigned (N.v39898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39898 s i)) at 1.
  unfold R.v39898, N.v39898.
  rewrite ?node_7395.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39899 (s : N.State) (i : N.Inputs) :
  R.v39899 (state s) (inputs i) = Zmod.unsigned (N.v39899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39899 s i)) at 1.
  unfold R.v39899, N.v39899.
  unfold R.v6, N.v6.
  rewrite ?node_7513.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39900 (s : N.State) (i : N.Inputs) :
  R.v39900 (state s) (inputs i) = Zmod.unsigned (N.v39900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39900 s i)) at 1.
  unfold R.v39900, N.v39900.
  rewrite ?node_39898.
  rewrite ?node_39899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39901 (s : N.State) (i : N.Inputs) :
  R.v39901 (state s) (inputs i) = Zmod.unsigned (N.v39901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39901 s i)) at 1.
  unfold R.v39901, N.v39901.
  rewrite ?node_39897.
  rewrite ?node_39900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39902 (s : N.State) (i : N.Inputs) :
  R.v39902 (state s) (inputs i) = Zmod.unsigned (N.v39902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39902 s i)) at 1.
  unfold R.v39902, N.v39902.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39903 (s : N.State) (i : N.Inputs) :
  R.v39903 (state s) (inputs i) = Zmod.unsigned (N.v39903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39903 s i)) at 1.
  unfold R.v39903, N.v39903.
  rewrite ?node_7406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39904 (s : N.State) (i : N.Inputs) :
  R.v39904 (state s) (inputs i) = Zmod.unsigned (N.v39904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39904 s i)) at 1.
  unfold R.v39904, N.v39904.
  unfold R.v6, N.v6.
  rewrite ?node_7402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39905 (s : N.State) (i : N.Inputs) :
  R.v39905 (state s) (inputs i) = Zmod.unsigned (N.v39905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39905 s i)) at 1.
  unfold R.v39905, N.v39905.
  unfold R.v6, N.v6.
  rewrite ?node_7395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39906 (s : N.State) (i : N.Inputs) :
  R.v39906 (state s) (inputs i) = Zmod.unsigned (N.v39906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39906 s i)) at 1.
  unfold R.v39906, N.v39906.
  rewrite ?node_39904.
  rewrite ?node_39905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39907 (s : N.State) (i : N.Inputs) :
  R.v39907 (state s) (inputs i) = Zmod.unsigned (N.v39907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39907 s i)) at 1.
  unfold R.v39907, N.v39907.
  unfold R.v16484, N.v16484.
  rewrite ?node_39906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39908 (s : N.State) (i : N.Inputs) :
  R.v39908 (state s) (inputs i) = Zmod.unsigned (N.v39908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39908 s i)) at 1.
  unfold R.v39908, N.v39908.
  rewrite ?node_39903.
  rewrite ?node_39907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39909 (s : N.State) (i : N.Inputs) :
  R.v39909 (state s) (inputs i) = Zmod.unsigned (N.v39909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39909 s i)) at 1.
  unfold R.v39909, N.v39909.
  unfold R.v6, N.v6.
  rewrite ?node_39908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39910 (s : N.State) (i : N.Inputs) :
  R.v39910 (state s) (inputs i) = Zmod.unsigned (N.v39910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39910 s i)) at 1.
  unfold R.v39910, N.v39910.
  rewrite ?node_7407.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39911 (s : N.State) (i : N.Inputs) :
  R.v39911 (state s) (inputs i) = Zmod.unsigned (N.v39911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39911 s i)) at 1.
  unfold R.v39911, N.v39911.
  unfold R.v6, N.v6.
  rewrite ?node_7560.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39912 (s : N.State) (i : N.Inputs) :
  R.v39912 (state s) (inputs i) = Zmod.unsigned (N.v39912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39912 s i)) at 1.
  unfold R.v39912, N.v39912.
  rewrite ?node_39910.
  rewrite ?node_39911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39913 (s : N.State) (i : N.Inputs) :
  R.v39913 (state s) (inputs i) = Zmod.unsigned (N.v39913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39913 s i)) at 1.
  unfold R.v39913, N.v39913.
  rewrite ?node_39909.
  rewrite ?node_39912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39914 (s : N.State) (i : N.Inputs) :
  R.v39914 (state s) (inputs i) = Zmod.unsigned (N.v39914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39914 s i)) at 1.
  unfold R.v39914, N.v39914.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39915 (s : N.State) (i : N.Inputs) :
  R.v39915 (state s) (inputs i) = Zmod.unsigned (N.v39915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39915 s i)) at 1.
  unfold R.v39915, N.v39915.
  rewrite ?node_7428.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39916 (s : N.State) (i : N.Inputs) :
  R.v39916 (state s) (inputs i) = Zmod.unsigned (N.v39916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39916 s i)) at 1.
  unfold R.v39916, N.v39916.
  rewrite ?node_7424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39917 (s : N.State) (i : N.Inputs) :
  R.v39917 (state s) (inputs i) = Zmod.unsigned (N.v39917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39917 s i)) at 1.
  unfold R.v39917, N.v39917.
  rewrite ?node_7420.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39918 (s : N.State) (i : N.Inputs) :
  R.v39918 (state s) (inputs i) = Zmod.unsigned (N.v39918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39918 s i)) at 1.
  unfold R.v39918, N.v39918.
  unfold R.v6, N.v6.
  rewrite ?node_7416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39919 (s : N.State) (i : N.Inputs) :
  R.v39919 (state s) (inputs i) = Zmod.unsigned (N.v39919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39919 s i)) at 1.
  unfold R.v39919, N.v39919.
  unfold R.v6, N.v6.
  rewrite ?node_7414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39920 (s : N.State) (i : N.Inputs) :
  R.v39920 (state s) (inputs i) = Zmod.unsigned (N.v39920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39920 s i)) at 1.
  unfold R.v39920, N.v39920.
  rewrite ?node_39918.
  rewrite ?node_39919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39921 (s : N.State) (i : N.Inputs) :
  R.v39921 (state s) (inputs i) = Zmod.unsigned (N.v39921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39921 s i)) at 1.
  unfold R.v39921, N.v39921.
  unfold R.v16484, N.v16484.
  rewrite ?node_39920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39922 (s : N.State) (i : N.Inputs) :
  R.v39922 (state s) (inputs i) = Zmod.unsigned (N.v39922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39922 s i)) at 1.
  unfold R.v39922, N.v39922.
  rewrite ?node_39915.
  rewrite ?node_39916.
  rewrite ?node_39917.
  rewrite ?node_39921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39923 (s : N.State) (i : N.Inputs) :
  R.v39923 (state s) (inputs i) = Zmod.unsigned (N.v39923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39923 s i)) at 1.
  unfold R.v39923, N.v39923.
  unfold R.v6, N.v6.
  rewrite ?node_39922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39924 (s : N.State) (i : N.Inputs) :
  R.v39924 (state s) (inputs i) = Zmod.unsigned (N.v39924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39924 s i)) at 1.
  unfold R.v39924, N.v39924.
  rewrite ?node_7429.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39925 (s : N.State) (i : N.Inputs) :
  R.v39925 (state s) (inputs i) = Zmod.unsigned (N.v39925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39925 s i)) at 1.
  unfold R.v39925, N.v39925.
  unfold R.v6, N.v6.
  rewrite ?node_7535.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39926 (s : N.State) (i : N.Inputs) :
  R.v39926 (state s) (inputs i) = Zmod.unsigned (N.v39926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39926 s i)) at 1.
  unfold R.v39926, N.v39926.
  unfold R.v6, N.v6.
  rewrite ?node_7568.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39927 (s : N.State) (i : N.Inputs) :
  R.v39927 (state s) (inputs i) = Zmod.unsigned (N.v39927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39927 s i)) at 1.
  unfold R.v39927, N.v39927.
  rewrite ?node_39924.
  rewrite ?node_39925.
  rewrite ?node_39926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39928 (s : N.State) (i : N.Inputs) :
  R.v39928 (state s) (inputs i) = Zmod.unsigned (N.v39928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39928 s i)) at 1.
  unfold R.v39928, N.v39928.
  rewrite ?node_39923.
  rewrite ?node_39927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39929 (s : N.State) (i : N.Inputs) :
  R.v39929 (state s) (inputs i) = Zmod.unsigned (N.v39929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39929 s i)) at 1.
  unfold R.v39929, N.v39929.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39930 (s : N.State) (i : N.Inputs) :
  R.v39930 (state s) (inputs i) = Zmod.unsigned (N.v39930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39930 s i)) at 1.
  unfold R.v39930, N.v39930.
  rewrite ?node_7420.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39931 (s : N.State) (i : N.Inputs) :
  R.v39931 (state s) (inputs i) = Zmod.unsigned (N.v39931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39931 s i)) at 1.
  unfold R.v39931, N.v39931.
  unfold R.v6, N.v6.
  rewrite ?node_7416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39932 (s : N.State) (i : N.Inputs) :
  R.v39932 (state s) (inputs i) = Zmod.unsigned (N.v39932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39932 s i)) at 1.
  unfold R.v39932, N.v39932.
  unfold R.v6, N.v6.
  rewrite ?node_7414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39933 (s : N.State) (i : N.Inputs) :
  R.v39933 (state s) (inputs i) = Zmod.unsigned (N.v39933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39933 s i)) at 1.
  unfold R.v39933, N.v39933.
  rewrite ?node_39931.
  rewrite ?node_39932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39934 (s : N.State) (i : N.Inputs) :
  R.v39934 (state s) (inputs i) = Zmod.unsigned (N.v39934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39934 s i)) at 1.
  unfold R.v39934, N.v39934.
  unfold R.v16484, N.v16484.
  rewrite ?node_39933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39935 (s : N.State) (i : N.Inputs) :
  R.v39935 (state s) (inputs i) = Zmod.unsigned (N.v39935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39935 s i)) at 1.
  unfold R.v39935, N.v39935.
  rewrite ?node_39930.
  rewrite ?node_39934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39936 (s : N.State) (i : N.Inputs) :
  R.v39936 (state s) (inputs i) = Zmod.unsigned (N.v39936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39936 s i)) at 1.
  unfold R.v39936, N.v39936.
  unfold R.v6, N.v6.
  rewrite ?node_39935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39937 (s : N.State) (i : N.Inputs) :
  R.v39937 (state s) (inputs i) = Zmod.unsigned (N.v39937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39937 s i)) at 1.
  unfold R.v39937, N.v39937.
  rewrite ?node_7421.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39938 (s : N.State) (i : N.Inputs) :
  R.v39938 (state s) (inputs i) = Zmod.unsigned (N.v39938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39938 s i)) at 1.
  unfold R.v39938, N.v39938.
  unfold R.v6, N.v6.
  rewrite ?node_7535.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39939 (s : N.State) (i : N.Inputs) :
  R.v39939 (state s) (inputs i) = Zmod.unsigned (N.v39939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39939 s i)) at 1.
  unfold R.v39939, N.v39939.
  rewrite ?node_39937.
  rewrite ?node_39938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39940 (s : N.State) (i : N.Inputs) :
  R.v39940 (state s) (inputs i) = Zmod.unsigned (N.v39940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39940 s i)) at 1.
  unfold R.v39940, N.v39940.
  rewrite ?node_39936.
  rewrite ?node_39939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39941 (s : N.State) (i : N.Inputs) :
  R.v39941 (state s) (inputs i) = Zmod.unsigned (N.v39941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39941 s i)) at 1.
  unfold R.v39941, N.v39941.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39942 (s : N.State) (i : N.Inputs) :
  R.v39942 (state s) (inputs i) = Zmod.unsigned (N.v39942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39942 s i)) at 1.
  unfold R.v39942, N.v39942.
  rewrite ?node_7428.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39943 (s : N.State) (i : N.Inputs) :
  R.v39943 (state s) (inputs i) = Zmod.unsigned (N.v39943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39943 s i)) at 1.
  unfold R.v39943, N.v39943.
  unfold R.v6, N.v6.
  rewrite ?node_7424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39944 (s : N.State) (i : N.Inputs) :
  R.v39944 (state s) (inputs i) = Zmod.unsigned (N.v39944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39944 s i)) at 1.
  unfold R.v39944, N.v39944.
  unfold R.v6, N.v6.
  rewrite ?node_7421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39945 (s : N.State) (i : N.Inputs) :
  R.v39945 (state s) (inputs i) = Zmod.unsigned (N.v39945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39945 s i)) at 1.
  unfold R.v39945, N.v39945.
  rewrite ?node_39943.
  rewrite ?node_39944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39946 (s : N.State) (i : N.Inputs) :
  R.v39946 (state s) (inputs i) = Zmod.unsigned (N.v39946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39946 s i)) at 1.
  unfold R.v39946, N.v39946.
  unfold R.v16484, N.v16484.
  rewrite ?node_39945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39947 (s : N.State) (i : N.Inputs) :
  R.v39947 (state s) (inputs i) = Zmod.unsigned (N.v39947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39947 s i)) at 1.
  unfold R.v39947, N.v39947.
  rewrite ?node_39942.
  rewrite ?node_39946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39948 (s : N.State) (i : N.Inputs) :
  R.v39948 (state s) (inputs i) = Zmod.unsigned (N.v39948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39948 s i)) at 1.
  unfold R.v39948, N.v39948.
  unfold R.v6, N.v6.
  rewrite ?node_39947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39949 (s : N.State) (i : N.Inputs) :
  R.v39949 (state s) (inputs i) = Zmod.unsigned (N.v39949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39949 s i)) at 1.
  unfold R.v39949, N.v39949.
  rewrite ?node_7429.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39950 (s : N.State) (i : N.Inputs) :
  R.v39950 (state s) (inputs i) = Zmod.unsigned (N.v39950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39950 s i)) at 1.
  unfold R.v39950, N.v39950.
  unfold R.v6, N.v6.
  rewrite ?node_7568.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39951 (s : N.State) (i : N.Inputs) :
  R.v39951 (state s) (inputs i) = Zmod.unsigned (N.v39951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39951 s i)) at 1.
  unfold R.v39951, N.v39951.
  rewrite ?node_39949.
  rewrite ?node_39950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39952 (s : N.State) (i : N.Inputs) :
  R.v39952 (state s) (inputs i) = Zmod.unsigned (N.v39952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39952 s i)) at 1.
  unfold R.v39952, N.v39952.
  rewrite ?node_39948.
  rewrite ?node_39951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39953 (s : N.State) (i : N.Inputs) :
  R.v39953 (state s) (inputs i) = Zmod.unsigned (N.v39953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39953 s i)) at 1.
  unfold R.v39953, N.v39953.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39954 (s : N.State) (i : N.Inputs) :
  R.v39954 (state s) (inputs i) = Zmod.unsigned (N.v39954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39954 s i)) at 1.
  unfold R.v39954, N.v39954.
  rewrite ?node_7446.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39955 (s : N.State) (i : N.Inputs) :
  R.v39955 (state s) (inputs i) = Zmod.unsigned (N.v39955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39955 s i)) at 1.
  unfold R.v39955, N.v39955.
  rewrite ?node_7442.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39956 (s : N.State) (i : N.Inputs) :
  R.v39956 (state s) (inputs i) = Zmod.unsigned (N.v39956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39956 s i)) at 1.
  unfold R.v39956, N.v39956.
  rewrite ?node_7440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39957 (s : N.State) (i : N.Inputs) :
  R.v39957 (state s) (inputs i) = Zmod.unsigned (N.v39957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39957 s i)) at 1.
  unfold R.v39957, N.v39957.
  unfold R.v6, N.v6.
  rewrite ?node_7436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39958 (s : N.State) (i : N.Inputs) :
  R.v39958 (state s) (inputs i) = Zmod.unsigned (N.v39958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39958 s i)) at 1.
  unfold R.v39958, N.v39958.
  unfold R.v6, N.v6.
  rewrite ?node_7433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39959 (s : N.State) (i : N.Inputs) :
  R.v39959 (state s) (inputs i) = Zmod.unsigned (N.v39959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39959 s i)) at 1.
  unfold R.v39959, N.v39959.
  rewrite ?node_39957.
  rewrite ?node_39958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39960 (s : N.State) (i : N.Inputs) :
  R.v39960 (state s) (inputs i) = Zmod.unsigned (N.v39960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39960 s i)) at 1.
  unfold R.v39960, N.v39960.
  unfold R.v16484, N.v16484.
  rewrite ?node_39959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39961 (s : N.State) (i : N.Inputs) :
  R.v39961 (state s) (inputs i) = Zmod.unsigned (N.v39961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39961 s i)) at 1.
  unfold R.v39961, N.v39961.
  rewrite ?node_39954.
  rewrite ?node_39955.
  rewrite ?node_39956.
  rewrite ?node_39960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39962 (s : N.State) (i : N.Inputs) :
  R.v39962 (state s) (inputs i) = Zmod.unsigned (N.v39962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39962 s i)) at 1.
  unfold R.v39962, N.v39962.
  unfold R.v6, N.v6.
  rewrite ?node_39961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39963 (s : N.State) (i : N.Inputs) :
  R.v39963 (state s) (inputs i) = Zmod.unsigned (N.v39963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39963 s i)) at 1.
  unfold R.v39963, N.v39963.
  rewrite ?node_7447.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39964 (s : N.State) (i : N.Inputs) :
  R.v39964 (state s) (inputs i) = Zmod.unsigned (N.v39964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39964 s i)) at 1.
  unfold R.v39964, N.v39964.
  unfold R.v6, N.v6.
  rewrite ?node_7555.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39965 (s : N.State) (i : N.Inputs) :
  R.v39965 (state s) (inputs i) = Zmod.unsigned (N.v39965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39965 s i)) at 1.
  unfold R.v39965, N.v39965.
  unfold R.v6, N.v6.
  rewrite ?node_7571.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39966 (s : N.State) (i : N.Inputs) :
  R.v39966 (state s) (inputs i) = Zmod.unsigned (N.v39966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39966 s i)) at 1.
  unfold R.v39966, N.v39966.
  rewrite ?node_39963.
  rewrite ?node_39964.
  rewrite ?node_39965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39967 (s : N.State) (i : N.Inputs) :
  R.v39967 (state s) (inputs i) = Zmod.unsigned (N.v39967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39967 s i)) at 1.
  unfold R.v39967, N.v39967.
  rewrite ?node_39962.
  rewrite ?node_39966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39968 (s : N.State) (i : N.Inputs) :
  R.v39968 (state s) (inputs i) = Zmod.unsigned (N.v39968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39968 s i)) at 1.
  unfold R.v39968, N.v39968.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39969 (s : N.State) (i : N.Inputs) :
  R.v39969 (state s) (inputs i) = Zmod.unsigned (N.v39969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39969 s i)) at 1.
  unfold R.v39969, N.v39969.
  rewrite ?node_7440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39970 (s : N.State) (i : N.Inputs) :
  R.v39970 (state s) (inputs i) = Zmod.unsigned (N.v39970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39970 s i)) at 1.
  unfold R.v39970, N.v39970.
  unfold R.v6, N.v6.
  rewrite ?node_7436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39971 (s : N.State) (i : N.Inputs) :
  R.v39971 (state s) (inputs i) = Zmod.unsigned (N.v39971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39971 s i)) at 1.
  unfold R.v39971, N.v39971.
  unfold R.v6, N.v6.
  rewrite ?node_7433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39972 (s : N.State) (i : N.Inputs) :
  R.v39972 (state s) (inputs i) = Zmod.unsigned (N.v39972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39972 s i)) at 1.
  unfold R.v39972, N.v39972.
  rewrite ?node_39970.
  rewrite ?node_39971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39973 (s : N.State) (i : N.Inputs) :
  R.v39973 (state s) (inputs i) = Zmod.unsigned (N.v39973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39973 s i)) at 1.
  unfold R.v39973, N.v39973.
  unfold R.v16484, N.v16484.
  rewrite ?node_39972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39974 (s : N.State) (i : N.Inputs) :
  R.v39974 (state s) (inputs i) = Zmod.unsigned (N.v39974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39974 s i)) at 1.
  unfold R.v39974, N.v39974.
  rewrite ?node_39969.
  rewrite ?node_39973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39975 (s : N.State) (i : N.Inputs) :
  R.v39975 (state s) (inputs i) = Zmod.unsigned (N.v39975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39975 s i)) at 1.
  unfold R.v39975, N.v39975.
  unfold R.v6, N.v6.
  rewrite ?node_39974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39976 (s : N.State) (i : N.Inputs) :
  R.v39976 (state s) (inputs i) = Zmod.unsigned (N.v39976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39976 s i)) at 1.
  unfold R.v39976, N.v39976.
  rewrite ?node_7441.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39977 (s : N.State) (i : N.Inputs) :
  R.v39977 (state s) (inputs i) = Zmod.unsigned (N.v39977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39977 s i)) at 1.
  unfold R.v39977, N.v39977.
  unfold R.v6, N.v6.
  rewrite ?node_7555.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39978 (s : N.State) (i : N.Inputs) :
  R.v39978 (state s) (inputs i) = Zmod.unsigned (N.v39978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39978 s i)) at 1.
  unfold R.v39978, N.v39978.
  rewrite ?node_39976.
  rewrite ?node_39977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39979 (s : N.State) (i : N.Inputs) :
  R.v39979 (state s) (inputs i) = Zmod.unsigned (N.v39979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39979 s i)) at 1.
  unfold R.v39979, N.v39979.
  rewrite ?node_39975.
  rewrite ?node_39978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39980 (s : N.State) (i : N.Inputs) :
  R.v39980 (state s) (inputs i) = Zmod.unsigned (N.v39980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39980 s i)) at 1.
  unfold R.v39980, N.v39980.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39981 (s : N.State) (i : N.Inputs) :
  R.v39981 (state s) (inputs i) = Zmod.unsigned (N.v39981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39981 s i)) at 1.
  unfold R.v39981, N.v39981.
  rewrite ?node_7446.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39982 (s : N.State) (i : N.Inputs) :
  R.v39982 (state s) (inputs i) = Zmod.unsigned (N.v39982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39982 s i)) at 1.
  unfold R.v39982, N.v39982.
  unfold R.v6, N.v6.
  rewrite ?node_7442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39983 (s : N.State) (i : N.Inputs) :
  R.v39983 (state s) (inputs i) = Zmod.unsigned (N.v39983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39983 s i)) at 1.
  unfold R.v39983, N.v39983.
  unfold R.v6, N.v6.
  rewrite ?node_7441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39984 (s : N.State) (i : N.Inputs) :
  R.v39984 (state s) (inputs i) = Zmod.unsigned (N.v39984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39984 s i)) at 1.
  unfold R.v39984, N.v39984.
  rewrite ?node_39982.
  rewrite ?node_39983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39985 (s : N.State) (i : N.Inputs) :
  R.v39985 (state s) (inputs i) = Zmod.unsigned (N.v39985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39985 s i)) at 1.
  unfold R.v39985, N.v39985.
  unfold R.v16484, N.v16484.
  rewrite ?node_39984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39986 (s : N.State) (i : N.Inputs) :
  R.v39986 (state s) (inputs i) = Zmod.unsigned (N.v39986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39986 s i)) at 1.
  unfold R.v39986, N.v39986.
  rewrite ?node_39981.
  rewrite ?node_39985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39987 (s : N.State) (i : N.Inputs) :
  R.v39987 (state s) (inputs i) = Zmod.unsigned (N.v39987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39987 s i)) at 1.
  unfold R.v39987, N.v39987.
  unfold R.v6, N.v6.
  rewrite ?node_39986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39988 (s : N.State) (i : N.Inputs) :
  R.v39988 (state s) (inputs i) = Zmod.unsigned (N.v39988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39988 s i)) at 1.
  unfold R.v39988, N.v39988.
  rewrite ?node_7447.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39989 (s : N.State) (i : N.Inputs) :
  R.v39989 (state s) (inputs i) = Zmod.unsigned (N.v39989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39989 s i)) at 1.
  unfold R.v39989, N.v39989.
  unfold R.v6, N.v6.
  rewrite ?node_7571.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39990 (s : N.State) (i : N.Inputs) :
  R.v39990 (state s) (inputs i) = Zmod.unsigned (N.v39990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39990 s i)) at 1.
  unfold R.v39990, N.v39990.
  rewrite ?node_39988.
  rewrite ?node_39989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39991 (s : N.State) (i : N.Inputs) :
  R.v39991 (state s) (inputs i) = Zmod.unsigned (N.v39991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39991 s i)) at 1.
  unfold R.v39991, N.v39991.
  rewrite ?node_39987.
  rewrite ?node_39990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39992 (s : N.State) (i : N.Inputs) :
  R.v39992 (state s) (inputs i) = Zmod.unsigned (N.v39992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39992 s i)) at 1.
  unfold R.v39992, N.v39992.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39993 (s : N.State) (i : N.Inputs) :
  R.v39993 (state s) (inputs i) = Zmod.unsigned (N.v39993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39993 s i)) at 1.
  unfold R.v39993, N.v39993.
  rewrite ?node_7513.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39994 (s : N.State) (i : N.Inputs) :
  R.v39994 (state s) (inputs i) = Zmod.unsigned (N.v39994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39994 s i)) at 1.
  unfold R.v39994, N.v39994.
  rewrite ?node_7509.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39995 (s : N.State) (i : N.Inputs) :
  R.v39995 (state s) (inputs i) = Zmod.unsigned (N.v39995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39995 s i)) at 1.
  unfold R.v39995, N.v39995.
  rewrite ?node_7501.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39996 (s : N.State) (i : N.Inputs) :
  R.v39996 (state s) (inputs i) = Zmod.unsigned (N.v39996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39996 s i)) at 1.
  unfold R.v39996, N.v39996.
  unfold R.v6, N.v6.
  rewrite ?node_7493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39997 (s : N.State) (i : N.Inputs) :
  R.v39997 (state s) (inputs i) = Zmod.unsigned (N.v39997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39997 s i)) at 1.
  unfold R.v39997, N.v39997.
  unfold R.v6, N.v6.
  rewrite ?node_7486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39998 (s : N.State) (i : N.Inputs) :
  R.v39998 (state s) (inputs i) = Zmod.unsigned (N.v39998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39998 s i)) at 1.
  unfold R.v39998, N.v39998.
  rewrite ?node_39996.
  rewrite ?node_39997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39999 (s : N.State) (i : N.Inputs) :
  R.v39999 (state s) (inputs i) = Zmod.unsigned (N.v39999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39999 s i)) at 1.
  unfold R.v39999, N.v39999.
  unfold R.v16484, N.v16484.
  rewrite ?node_39998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
