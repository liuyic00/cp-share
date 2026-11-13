(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes048.
Lemma node_49000 (s : N.State) (i : N.Inputs) :
  R.v49000 (state s) (inputs i) = Zmod.unsigned (N.v49000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49000 s i)) at 1.
  unfold R.v49000, N.v49000.
  rewrite ?node_48995.
  rewrite ?node_48999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49001 (s : N.State) (i : N.Inputs) :
  R.v49001 (state s) (inputs i) = Zmod.unsigned (N.v49001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49001 s i)) at 1.
  unfold R.v49001, N.v49001.
  unfold R.v6, N.v6.
  rewrite ?node_49000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49002 (s : N.State) (i : N.Inputs) :
  R.v49002 (state s) (inputs i) = Zmod.unsigned (N.v49002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49002 s i)) at 1.
  unfold R.v49002, N.v49002.
  rewrite ?node_5929.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49003 (s : N.State) (i : N.Inputs) :
  R.v49003 (state s) (inputs i) = Zmod.unsigned (N.v49003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49003 s i)) at 1.
  unfold R.v49003, N.v49003.
  unfold R.v6, N.v6.
  rewrite ?node_5996.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49004 (s : N.State) (i : N.Inputs) :
  R.v49004 (state s) (inputs i) = Zmod.unsigned (N.v49004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49004 s i)) at 1.
  unfold R.v49004, N.v49004.
  rewrite ?node_49002.
  rewrite ?node_49003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49005 (s : N.State) (i : N.Inputs) :
  R.v49005 (state s) (inputs i) = Zmod.unsigned (N.v49005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49005 s i)) at 1.
  unfold R.v49005, N.v49005.
  rewrite ?node_49001.
  rewrite ?node_49004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49006 (s : N.State) (i : N.Inputs) :
  R.v49006 (state s) (inputs i) = Zmod.unsigned (N.v49006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49006 s i)) at 1.
  unfold R.v49006, N.v49006.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49007 (s : N.State) (i : N.Inputs) :
  R.v49007 (state s) (inputs i) = Zmod.unsigned (N.v49007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49007 s i)) at 1.
  unfold R.v49007, N.v49007.
  rewrite ?node_5992.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49008 (s : N.State) (i : N.Inputs) :
  R.v49008 (state s) (inputs i) = Zmod.unsigned (N.v49008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49008 s i)) at 1.
  unfold R.v49008, N.v49008.
  rewrite ?node_5988.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49009 (s : N.State) (i : N.Inputs) :
  R.v49009 (state s) (inputs i) = Zmod.unsigned (N.v49009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49009 s i)) at 1.
  unfold R.v49009, N.v49009.
  rewrite ?node_5984.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49010 (s : N.State) (i : N.Inputs) :
  R.v49010 (state s) (inputs i) = Zmod.unsigned (N.v49010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49010 s i)) at 1.
  unfold R.v49010, N.v49010.
  unfold R.v6, N.v6.
  rewrite ?node_5980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49011 (s : N.State) (i : N.Inputs) :
  R.v49011 (state s) (inputs i) = Zmod.unsigned (N.v49011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49011 s i)) at 1.
  unfold R.v49011, N.v49011.
  unfold R.v6, N.v6.
  rewrite ?node_5967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49012 (s : N.State) (i : N.Inputs) :
  R.v49012 (state s) (inputs i) = Zmod.unsigned (N.v49012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49012 s i)) at 1.
  unfold R.v49012, N.v49012.
  rewrite ?node_49010.
  rewrite ?node_49011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49013 (s : N.State) (i : N.Inputs) :
  R.v49013 (state s) (inputs i) = Zmod.unsigned (N.v49013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49013 s i)) at 1.
  unfold R.v49013, N.v49013.
  unfold R.v16484, N.v16484.
  rewrite ?node_49012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49014 (s : N.State) (i : N.Inputs) :
  R.v49014 (state s) (inputs i) = Zmod.unsigned (N.v49014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49014 s i)) at 1.
  unfold R.v49014, N.v49014.
  rewrite ?node_49007.
  rewrite ?node_49008.
  rewrite ?node_49009.
  rewrite ?node_49013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49015 (s : N.State) (i : N.Inputs) :
  R.v49015 (state s) (inputs i) = Zmod.unsigned (N.v49015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49015 s i)) at 1.
  unfold R.v49015, N.v49015.
  unfold R.v6, N.v6.
  rewrite ?node_49014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49016 (s : N.State) (i : N.Inputs) :
  R.v49016 (state s) (inputs i) = Zmod.unsigned (N.v49016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49016 s i)) at 1.
  unfold R.v49016, N.v49016.
  rewrite ?node_5993.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49017 (s : N.State) (i : N.Inputs) :
  R.v49017 (state s) (inputs i) = Zmod.unsigned (N.v49017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49017 s i)) at 1.
  unfold R.v49017, N.v49017.
  unfold R.v6, N.v6.
  rewrite ?node_6059.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49018 (s : N.State) (i : N.Inputs) :
  R.v49018 (state s) (inputs i) = Zmod.unsigned (N.v49018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49018 s i)) at 1.
  unfold R.v49018, N.v49018.
  unfold R.v6, N.v6.
  rewrite ?node_6063.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49019 (s : N.State) (i : N.Inputs) :
  R.v49019 (state s) (inputs i) = Zmod.unsigned (N.v49019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49019 s i)) at 1.
  unfold R.v49019, N.v49019.
  rewrite ?node_49016.
  rewrite ?node_49017.
  rewrite ?node_49018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49020 (s : N.State) (i : N.Inputs) :
  R.v49020 (state s) (inputs i) = Zmod.unsigned (N.v49020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49020 s i)) at 1.
  unfold R.v49020, N.v49020.
  rewrite ?node_49015.
  rewrite ?node_49019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49021 (s : N.State) (i : N.Inputs) :
  R.v49021 (state s) (inputs i) = Zmod.unsigned (N.v49021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49021 s i)) at 1.
  unfold R.v49021, N.v49021.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49022 (s : N.State) (i : N.Inputs) :
  R.v49022 (state s) (inputs i) = Zmod.unsigned (N.v49022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49022 s i)) at 1.
  unfold R.v49022, N.v49022.
  rewrite ?node_5984.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49023 (s : N.State) (i : N.Inputs) :
  R.v49023 (state s) (inputs i) = Zmod.unsigned (N.v49023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49023 s i)) at 1.
  unfold R.v49023, N.v49023.
  unfold R.v6, N.v6.
  rewrite ?node_5980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49024 (s : N.State) (i : N.Inputs) :
  R.v49024 (state s) (inputs i) = Zmod.unsigned (N.v49024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49024 s i)) at 1.
  unfold R.v49024, N.v49024.
  unfold R.v6, N.v6.
  rewrite ?node_5967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49025 (s : N.State) (i : N.Inputs) :
  R.v49025 (state s) (inputs i) = Zmod.unsigned (N.v49025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49025 s i)) at 1.
  unfold R.v49025, N.v49025.
  rewrite ?node_49023.
  rewrite ?node_49024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49026 (s : N.State) (i : N.Inputs) :
  R.v49026 (state s) (inputs i) = Zmod.unsigned (N.v49026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49026 s i)) at 1.
  unfold R.v49026, N.v49026.
  unfold R.v16484, N.v16484.
  rewrite ?node_49025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49027 (s : N.State) (i : N.Inputs) :
  R.v49027 (state s) (inputs i) = Zmod.unsigned (N.v49027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49027 s i)) at 1.
  unfold R.v49027, N.v49027.
  rewrite ?node_49022.
  rewrite ?node_49026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49028 (s : N.State) (i : N.Inputs) :
  R.v49028 (state s) (inputs i) = Zmod.unsigned (N.v49028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49028 s i)) at 1.
  unfold R.v49028, N.v49028.
  unfold R.v6, N.v6.
  rewrite ?node_49027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49029 (s : N.State) (i : N.Inputs) :
  R.v49029 (state s) (inputs i) = Zmod.unsigned (N.v49029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49029 s i)) at 1.
  unfold R.v49029, N.v49029.
  rewrite ?node_5985.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49030 (s : N.State) (i : N.Inputs) :
  R.v49030 (state s) (inputs i) = Zmod.unsigned (N.v49030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49030 s i)) at 1.
  unfold R.v49030, N.v49030.
  unfold R.v6, N.v6.
  rewrite ?node_6059.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49031 (s : N.State) (i : N.Inputs) :
  R.v49031 (state s) (inputs i) = Zmod.unsigned (N.v49031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49031 s i)) at 1.
  unfold R.v49031, N.v49031.
  rewrite ?node_49029.
  rewrite ?node_49030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49032 (s : N.State) (i : N.Inputs) :
  R.v49032 (state s) (inputs i) = Zmod.unsigned (N.v49032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49032 s i)) at 1.
  unfold R.v49032, N.v49032.
  rewrite ?node_49028.
  rewrite ?node_49031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49033 (s : N.State) (i : N.Inputs) :
  R.v49033 (state s) (inputs i) = Zmod.unsigned (N.v49033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49033 s i)) at 1.
  unfold R.v49033, N.v49033.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49034 (s : N.State) (i : N.Inputs) :
  R.v49034 (state s) (inputs i) = Zmod.unsigned (N.v49034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49034 s i)) at 1.
  unfold R.v49034, N.v49034.
  rewrite ?node_5992.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49035 (s : N.State) (i : N.Inputs) :
  R.v49035 (state s) (inputs i) = Zmod.unsigned (N.v49035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49035 s i)) at 1.
  unfold R.v49035, N.v49035.
  unfold R.v6, N.v6.
  rewrite ?node_5988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49036 (s : N.State) (i : N.Inputs) :
  R.v49036 (state s) (inputs i) = Zmod.unsigned (N.v49036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49036 s i)) at 1.
  unfold R.v49036, N.v49036.
  unfold R.v6, N.v6.
  rewrite ?node_5985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49037 (s : N.State) (i : N.Inputs) :
  R.v49037 (state s) (inputs i) = Zmod.unsigned (N.v49037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49037 s i)) at 1.
  unfold R.v49037, N.v49037.
  rewrite ?node_49035.
  rewrite ?node_49036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49038 (s : N.State) (i : N.Inputs) :
  R.v49038 (state s) (inputs i) = Zmod.unsigned (N.v49038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49038 s i)) at 1.
  unfold R.v49038, N.v49038.
  unfold R.v16484, N.v16484.
  rewrite ?node_49037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49039 (s : N.State) (i : N.Inputs) :
  R.v49039 (state s) (inputs i) = Zmod.unsigned (N.v49039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49039 s i)) at 1.
  unfold R.v49039, N.v49039.
  rewrite ?node_49034.
  rewrite ?node_49038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49040 (s : N.State) (i : N.Inputs) :
  R.v49040 (state s) (inputs i) = Zmod.unsigned (N.v49040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49040 s i)) at 1.
  unfold R.v49040, N.v49040.
  unfold R.v6, N.v6.
  rewrite ?node_49039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49041 (s : N.State) (i : N.Inputs) :
  R.v49041 (state s) (inputs i) = Zmod.unsigned (N.v49041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49041 s i)) at 1.
  unfold R.v49041, N.v49041.
  rewrite ?node_5993.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49042 (s : N.State) (i : N.Inputs) :
  R.v49042 (state s) (inputs i) = Zmod.unsigned (N.v49042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49042 s i)) at 1.
  unfold R.v49042, N.v49042.
  unfold R.v6, N.v6.
  rewrite ?node_6063.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49043 (s : N.State) (i : N.Inputs) :
  R.v49043 (state s) (inputs i) = Zmod.unsigned (N.v49043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49043 s i)) at 1.
  unfold R.v49043, N.v49043.
  rewrite ?node_49041.
  rewrite ?node_49042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49044 (s : N.State) (i : N.Inputs) :
  R.v49044 (state s) (inputs i) = Zmod.unsigned (N.v49044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49044 s i)) at 1.
  unfold R.v49044, N.v49044.
  rewrite ?node_49040.
  rewrite ?node_49043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49045 (s : N.State) (i : N.Inputs) :
  R.v49045 (state s) (inputs i) = Zmod.unsigned (N.v49045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49045 s i)) at 1.
  unfold R.v49045, N.v49045.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49046 (s : N.State) (i : N.Inputs) :
  R.v49046 (state s) (inputs i) = Zmod.unsigned (N.v49046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49046 s i)) at 1.
  unfold R.v49046, N.v49046.
  rewrite ?node_6059.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49047 (s : N.State) (i : N.Inputs) :
  R.v49047 (state s) (inputs i) = Zmod.unsigned (N.v49047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49047 s i)) at 1.
  unfold R.v49047, N.v49047.
  rewrite ?node_6055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49048 (s : N.State) (i : N.Inputs) :
  R.v49048 (state s) (inputs i) = Zmod.unsigned (N.v49048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49048 s i)) at 1.
  unfold R.v49048, N.v49048.
  rewrite ?node_6053.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49049 (s : N.State) (i : N.Inputs) :
  R.v49049 (state s) (inputs i) = Zmod.unsigned (N.v49049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49049 s i)) at 1.
  unfold R.v49049, N.v49049.
  unfold R.v6, N.v6.
  rewrite ?node_6049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49050 (s : N.State) (i : N.Inputs) :
  R.v49050 (state s) (inputs i) = Zmod.unsigned (N.v49050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49050 s i)) at 1.
  unfold R.v49050, N.v49050.
  unfold R.v6, N.v6.
  rewrite ?node_6032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49051 (s : N.State) (i : N.Inputs) :
  R.v49051 (state s) (inputs i) = Zmod.unsigned (N.v49051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49051 s i)) at 1.
  unfold R.v49051, N.v49051.
  rewrite ?node_49049.
  rewrite ?node_49050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49052 (s : N.State) (i : N.Inputs) :
  R.v49052 (state s) (inputs i) = Zmod.unsigned (N.v49052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49052 s i)) at 1.
  unfold R.v49052, N.v49052.
  unfold R.v16484, N.v16484.
  rewrite ?node_49051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49053 (s : N.State) (i : N.Inputs) :
  R.v49053 (state s) (inputs i) = Zmod.unsigned (N.v49053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49053 s i)) at 1.
  unfold R.v49053, N.v49053.
  rewrite ?node_49046.
  rewrite ?node_49047.
  rewrite ?node_49048.
  rewrite ?node_49052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49054 (s : N.State) (i : N.Inputs) :
  R.v49054 (state s) (inputs i) = Zmod.unsigned (N.v49054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49054 s i)) at 1.
  unfold R.v49054, N.v49054.
  unfold R.v6, N.v6.
  rewrite ?node_49053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49055 (s : N.State) (i : N.Inputs) :
  R.v49055 (state s) (inputs i) = Zmod.unsigned (N.v49055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49055 s i)) at 1.
  unfold R.v49055, N.v49055.
  rewrite ?node_6060.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49056 (s : N.State) (i : N.Inputs) :
  R.v49056 (state s) (inputs i) = Zmod.unsigned (N.v49056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49056 s i)) at 1.
  unfold R.v49056, N.v49056.
  unfold R.v6, N.v6.
  rewrite ?node_6130.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49057 (s : N.State) (i : N.Inputs) :
  R.v49057 (state s) (inputs i) = Zmod.unsigned (N.v49057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49057 s i)) at 1.
  unfold R.v49057, N.v49057.
  unfold R.v6, N.v6.
  rewrite ?node_6134.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49058 (s : N.State) (i : N.Inputs) :
  R.v49058 (state s) (inputs i) = Zmod.unsigned (N.v49058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49058 s i)) at 1.
  unfold R.v49058, N.v49058.
  rewrite ?node_49055.
  rewrite ?node_49056.
  rewrite ?node_49057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49059 (s : N.State) (i : N.Inputs) :
  R.v49059 (state s) (inputs i) = Zmod.unsigned (N.v49059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49059 s i)) at 1.
  unfold R.v49059, N.v49059.
  rewrite ?node_49054.
  rewrite ?node_49058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49060 (s : N.State) (i : N.Inputs) :
  R.v49060 (state s) (inputs i) = Zmod.unsigned (N.v49060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49060 s i)) at 1.
  unfold R.v49060, N.v49060.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49061 (s : N.State) (i : N.Inputs) :
  R.v49061 (state s) (inputs i) = Zmod.unsigned (N.v49061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49061 s i)) at 1.
  unfold R.v49061, N.v49061.
  rewrite ?node_6053.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49062 (s : N.State) (i : N.Inputs) :
  R.v49062 (state s) (inputs i) = Zmod.unsigned (N.v49062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49062 s i)) at 1.
  unfold R.v49062, N.v49062.
  unfold R.v6, N.v6.
  rewrite ?node_6049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49063 (s : N.State) (i : N.Inputs) :
  R.v49063 (state s) (inputs i) = Zmod.unsigned (N.v49063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49063 s i)) at 1.
  unfold R.v49063, N.v49063.
  unfold R.v6, N.v6.
  rewrite ?node_6032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49064 (s : N.State) (i : N.Inputs) :
  R.v49064 (state s) (inputs i) = Zmod.unsigned (N.v49064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49064 s i)) at 1.
  unfold R.v49064, N.v49064.
  rewrite ?node_49062.
  rewrite ?node_49063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49065 (s : N.State) (i : N.Inputs) :
  R.v49065 (state s) (inputs i) = Zmod.unsigned (N.v49065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49065 s i)) at 1.
  unfold R.v49065, N.v49065.
  unfold R.v16484, N.v16484.
  rewrite ?node_49064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49066 (s : N.State) (i : N.Inputs) :
  R.v49066 (state s) (inputs i) = Zmod.unsigned (N.v49066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49066 s i)) at 1.
  unfold R.v49066, N.v49066.
  rewrite ?node_49061.
  rewrite ?node_49065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49067 (s : N.State) (i : N.Inputs) :
  R.v49067 (state s) (inputs i) = Zmod.unsigned (N.v49067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49067 s i)) at 1.
  unfold R.v49067, N.v49067.
  unfold R.v6, N.v6.
  rewrite ?node_49066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49068 (s : N.State) (i : N.Inputs) :
  R.v49068 (state s) (inputs i) = Zmod.unsigned (N.v49068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49068 s i)) at 1.
  unfold R.v49068, N.v49068.
  rewrite ?node_6054.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49069 (s : N.State) (i : N.Inputs) :
  R.v49069 (state s) (inputs i) = Zmod.unsigned (N.v49069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49069 s i)) at 1.
  unfold R.v49069, N.v49069.
  unfold R.v6, N.v6.
  rewrite ?node_6130.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49070 (s : N.State) (i : N.Inputs) :
  R.v49070 (state s) (inputs i) = Zmod.unsigned (N.v49070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49070 s i)) at 1.
  unfold R.v49070, N.v49070.
  rewrite ?node_49068.
  rewrite ?node_49069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49071 (s : N.State) (i : N.Inputs) :
  R.v49071 (state s) (inputs i) = Zmod.unsigned (N.v49071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49071 s i)) at 1.
  unfold R.v49071, N.v49071.
  rewrite ?node_49067.
  rewrite ?node_49070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49072 (s : N.State) (i : N.Inputs) :
  R.v49072 (state s) (inputs i) = Zmod.unsigned (N.v49072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49072 s i)) at 1.
  unfold R.v49072, N.v49072.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49073 (s : N.State) (i : N.Inputs) :
  R.v49073 (state s) (inputs i) = Zmod.unsigned (N.v49073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49073 s i)) at 1.
  unfold R.v49073, N.v49073.
  rewrite ?node_6059.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49074 (s : N.State) (i : N.Inputs) :
  R.v49074 (state s) (inputs i) = Zmod.unsigned (N.v49074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49074 s i)) at 1.
  unfold R.v49074, N.v49074.
  unfold R.v6, N.v6.
  rewrite ?node_6055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49075 (s : N.State) (i : N.Inputs) :
  R.v49075 (state s) (inputs i) = Zmod.unsigned (N.v49075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49075 s i)) at 1.
  unfold R.v49075, N.v49075.
  unfold R.v6, N.v6.
  rewrite ?node_6054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49076 (s : N.State) (i : N.Inputs) :
  R.v49076 (state s) (inputs i) = Zmod.unsigned (N.v49076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49076 s i)) at 1.
  unfold R.v49076, N.v49076.
  rewrite ?node_49074.
  rewrite ?node_49075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49077 (s : N.State) (i : N.Inputs) :
  R.v49077 (state s) (inputs i) = Zmod.unsigned (N.v49077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49077 s i)) at 1.
  unfold R.v49077, N.v49077.
  unfold R.v16484, N.v16484.
  rewrite ?node_49076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49078 (s : N.State) (i : N.Inputs) :
  R.v49078 (state s) (inputs i) = Zmod.unsigned (N.v49078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49078 s i)) at 1.
  unfold R.v49078, N.v49078.
  rewrite ?node_49073.
  rewrite ?node_49077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49079 (s : N.State) (i : N.Inputs) :
  R.v49079 (state s) (inputs i) = Zmod.unsigned (N.v49079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49079 s i)) at 1.
  unfold R.v49079, N.v49079.
  unfold R.v6, N.v6.
  rewrite ?node_49078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49080 (s : N.State) (i : N.Inputs) :
  R.v49080 (state s) (inputs i) = Zmod.unsigned (N.v49080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49080 s i)) at 1.
  unfold R.v49080, N.v49080.
  rewrite ?node_6060.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49081 (s : N.State) (i : N.Inputs) :
  R.v49081 (state s) (inputs i) = Zmod.unsigned (N.v49081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49081 s i)) at 1.
  unfold R.v49081, N.v49081.
  unfold R.v6, N.v6.
  rewrite ?node_6134.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49082 (s : N.State) (i : N.Inputs) :
  R.v49082 (state s) (inputs i) = Zmod.unsigned (N.v49082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49082 s i)) at 1.
  unfold R.v49082, N.v49082.
  rewrite ?node_49080.
  rewrite ?node_49081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49083 (s : N.State) (i : N.Inputs) :
  R.v49083 (state s) (inputs i) = Zmod.unsigned (N.v49083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49083 s i)) at 1.
  unfold R.v49083, N.v49083.
  rewrite ?node_49079.
  rewrite ?node_49082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49084 (s : N.State) (i : N.Inputs) :
  R.v49084 (state s) (inputs i) = Zmod.unsigned (N.v49084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49084 s i)) at 1.
  unfold R.v49084, N.v49084.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49085 (s : N.State) (i : N.Inputs) :
  R.v49085 (state s) (inputs i) = Zmod.unsigned (N.v49085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49085 s i)) at 1.
  unfold R.v49085, N.v49085.
  rewrite ?node_6130.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49086 (s : N.State) (i : N.Inputs) :
  R.v49086 (state s) (inputs i) = Zmod.unsigned (N.v49086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49086 s i)) at 1.
  unfold R.v49086, N.v49086.
  rewrite ?node_6126.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49087 (s : N.State) (i : N.Inputs) :
  R.v49087 (state s) (inputs i) = Zmod.unsigned (N.v49087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49087 s i)) at 1.
  unfold R.v49087, N.v49087.
  rewrite ?node_6122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49088 (s : N.State) (i : N.Inputs) :
  R.v49088 (state s) (inputs i) = Zmod.unsigned (N.v49088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49088 s i)) at 1.
  unfold R.v49088, N.v49088.
  unfold R.v6, N.v6.
  rewrite ?node_6118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49089 (s : N.State) (i : N.Inputs) :
  R.v49089 (state s) (inputs i) = Zmod.unsigned (N.v49089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49089 s i)) at 1.
  unfold R.v49089, N.v49089.
  unfold R.v6, N.v6.
  rewrite ?node_6099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49090 (s : N.State) (i : N.Inputs) :
  R.v49090 (state s) (inputs i) = Zmod.unsigned (N.v49090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49090 s i)) at 1.
  unfold R.v49090, N.v49090.
  rewrite ?node_49088.
  rewrite ?node_49089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49091 (s : N.State) (i : N.Inputs) :
  R.v49091 (state s) (inputs i) = Zmod.unsigned (N.v49091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49091 s i)) at 1.
  unfold R.v49091, N.v49091.
  unfold R.v16484, N.v16484.
  rewrite ?node_49090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49092 (s : N.State) (i : N.Inputs) :
  R.v49092 (state s) (inputs i) = Zmod.unsigned (N.v49092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49092 s i)) at 1.
  unfold R.v49092, N.v49092.
  rewrite ?node_49085.
  rewrite ?node_49086.
  rewrite ?node_49087.
  rewrite ?node_49091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49093 (s : N.State) (i : N.Inputs) :
  R.v49093 (state s) (inputs i) = Zmod.unsigned (N.v49093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49093 s i)) at 1.
  unfold R.v49093, N.v49093.
  unfold R.v6, N.v6.
  rewrite ?node_49092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49094 (s : N.State) (i : N.Inputs) :
  R.v49094 (state s) (inputs i) = Zmod.unsigned (N.v49094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49094 s i)) at 1.
  unfold R.v49094, N.v49094.
  rewrite ?node_6131.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49095 (s : N.State) (i : N.Inputs) :
  R.v49095 (state s) (inputs i) = Zmod.unsigned (N.v49095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49095 s i)) at 1.
  unfold R.v49095, N.v49095.
  unfold R.v6, N.v6.
  rewrite ?node_6202.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49096 (s : N.State) (i : N.Inputs) :
  R.v49096 (state s) (inputs i) = Zmod.unsigned (N.v49096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49096 s i)) at 1.
  unfold R.v49096, N.v49096.
  unfold R.v6, N.v6.
  rewrite ?node_6206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49097 (s : N.State) (i : N.Inputs) :
  R.v49097 (state s) (inputs i) = Zmod.unsigned (N.v49097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49097 s i)) at 1.
  unfold R.v49097, N.v49097.
  rewrite ?node_49094.
  rewrite ?node_49095.
  rewrite ?node_49096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49098 (s : N.State) (i : N.Inputs) :
  R.v49098 (state s) (inputs i) = Zmod.unsigned (N.v49098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49098 s i)) at 1.
  unfold R.v49098, N.v49098.
  rewrite ?node_49093.
  rewrite ?node_49097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49099 (s : N.State) (i : N.Inputs) :
  R.v49099 (state s) (inputs i) = Zmod.unsigned (N.v49099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49099 s i)) at 1.
  unfold R.v49099, N.v49099.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49100 (s : N.State) (i : N.Inputs) :
  R.v49100 (state s) (inputs i) = Zmod.unsigned (N.v49100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49100 s i)) at 1.
  unfold R.v49100, N.v49100.
  rewrite ?node_6122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49101 (s : N.State) (i : N.Inputs) :
  R.v49101 (state s) (inputs i) = Zmod.unsigned (N.v49101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49101 s i)) at 1.
  unfold R.v49101, N.v49101.
  unfold R.v6, N.v6.
  rewrite ?node_6118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49102 (s : N.State) (i : N.Inputs) :
  R.v49102 (state s) (inputs i) = Zmod.unsigned (N.v49102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49102 s i)) at 1.
  unfold R.v49102, N.v49102.
  unfold R.v6, N.v6.
  rewrite ?node_6099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49103 (s : N.State) (i : N.Inputs) :
  R.v49103 (state s) (inputs i) = Zmod.unsigned (N.v49103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49103 s i)) at 1.
  unfold R.v49103, N.v49103.
  rewrite ?node_49101.
  rewrite ?node_49102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49104 (s : N.State) (i : N.Inputs) :
  R.v49104 (state s) (inputs i) = Zmod.unsigned (N.v49104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49104 s i)) at 1.
  unfold R.v49104, N.v49104.
  unfold R.v16484, N.v16484.
  rewrite ?node_49103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49105 (s : N.State) (i : N.Inputs) :
  R.v49105 (state s) (inputs i) = Zmod.unsigned (N.v49105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49105 s i)) at 1.
  unfold R.v49105, N.v49105.
  rewrite ?node_49100.
  rewrite ?node_49104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49106 (s : N.State) (i : N.Inputs) :
  R.v49106 (state s) (inputs i) = Zmod.unsigned (N.v49106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49106 s i)) at 1.
  unfold R.v49106, N.v49106.
  unfold R.v6, N.v6.
  rewrite ?node_49105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49107 (s : N.State) (i : N.Inputs) :
  R.v49107 (state s) (inputs i) = Zmod.unsigned (N.v49107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49107 s i)) at 1.
  unfold R.v49107, N.v49107.
  rewrite ?node_6123.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49108 (s : N.State) (i : N.Inputs) :
  R.v49108 (state s) (inputs i) = Zmod.unsigned (N.v49108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49108 s i)) at 1.
  unfold R.v49108, N.v49108.
  unfold R.v6, N.v6.
  rewrite ?node_6202.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49109 (s : N.State) (i : N.Inputs) :
  R.v49109 (state s) (inputs i) = Zmod.unsigned (N.v49109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49109 s i)) at 1.
  unfold R.v49109, N.v49109.
  rewrite ?node_49107.
  rewrite ?node_49108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49110 (s : N.State) (i : N.Inputs) :
  R.v49110 (state s) (inputs i) = Zmod.unsigned (N.v49110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49110 s i)) at 1.
  unfold R.v49110, N.v49110.
  rewrite ?node_49106.
  rewrite ?node_49109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49111 (s : N.State) (i : N.Inputs) :
  R.v49111 (state s) (inputs i) = Zmod.unsigned (N.v49111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49111 s i)) at 1.
  unfold R.v49111, N.v49111.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49112 (s : N.State) (i : N.Inputs) :
  R.v49112 (state s) (inputs i) = Zmod.unsigned (N.v49112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49112 s i)) at 1.
  unfold R.v49112, N.v49112.
  rewrite ?node_6130.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49113 (s : N.State) (i : N.Inputs) :
  R.v49113 (state s) (inputs i) = Zmod.unsigned (N.v49113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49113 s i)) at 1.
  unfold R.v49113, N.v49113.
  unfold R.v6, N.v6.
  rewrite ?node_6126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49114 (s : N.State) (i : N.Inputs) :
  R.v49114 (state s) (inputs i) = Zmod.unsigned (N.v49114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49114 s i)) at 1.
  unfold R.v49114, N.v49114.
  unfold R.v6, N.v6.
  rewrite ?node_6123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49115 (s : N.State) (i : N.Inputs) :
  R.v49115 (state s) (inputs i) = Zmod.unsigned (N.v49115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49115 s i)) at 1.
  unfold R.v49115, N.v49115.
  rewrite ?node_49113.
  rewrite ?node_49114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49116 (s : N.State) (i : N.Inputs) :
  R.v49116 (state s) (inputs i) = Zmod.unsigned (N.v49116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49116 s i)) at 1.
  unfold R.v49116, N.v49116.
  unfold R.v16484, N.v16484.
  rewrite ?node_49115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49117 (s : N.State) (i : N.Inputs) :
  R.v49117 (state s) (inputs i) = Zmod.unsigned (N.v49117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49117 s i)) at 1.
  unfold R.v49117, N.v49117.
  rewrite ?node_49112.
  rewrite ?node_49116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49118 (s : N.State) (i : N.Inputs) :
  R.v49118 (state s) (inputs i) = Zmod.unsigned (N.v49118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49118 s i)) at 1.
  unfold R.v49118, N.v49118.
  unfold R.v6, N.v6.
  rewrite ?node_49117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49119 (s : N.State) (i : N.Inputs) :
  R.v49119 (state s) (inputs i) = Zmod.unsigned (N.v49119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49119 s i)) at 1.
  unfold R.v49119, N.v49119.
  rewrite ?node_6131.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49120 (s : N.State) (i : N.Inputs) :
  R.v49120 (state s) (inputs i) = Zmod.unsigned (N.v49120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49120 s i)) at 1.
  unfold R.v49120, N.v49120.
  unfold R.v6, N.v6.
  rewrite ?node_6206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49121 (s : N.State) (i : N.Inputs) :
  R.v49121 (state s) (inputs i) = Zmod.unsigned (N.v49121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49121 s i)) at 1.
  unfold R.v49121, N.v49121.
  rewrite ?node_49119.
  rewrite ?node_49120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49122 (s : N.State) (i : N.Inputs) :
  R.v49122 (state s) (inputs i) = Zmod.unsigned (N.v49122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49122 s i)) at 1.
  unfold R.v49122, N.v49122.
  rewrite ?node_49118.
  rewrite ?node_49121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49123 (s : N.State) (i : N.Inputs) :
  R.v49123 (state s) (inputs i) = Zmod.unsigned (N.v49123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49123 s i)) at 1.
  unfold R.v49123, N.v49123.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49124 (s : N.State) (i : N.Inputs) :
  R.v49124 (state s) (inputs i) = Zmod.unsigned (N.v49124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49124 s i)) at 1.
  unfold R.v49124, N.v49124.
  rewrite ?node_6202.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49125 (s : N.State) (i : N.Inputs) :
  R.v49125 (state s) (inputs i) = Zmod.unsigned (N.v49125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49125 s i)) at 1.
  unfold R.v49125, N.v49125.
  rewrite ?node_6198.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49126 (s : N.State) (i : N.Inputs) :
  R.v49126 (state s) (inputs i) = Zmod.unsigned (N.v49126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49126 s i)) at 1.
  unfold R.v49126, N.v49126.
  rewrite ?node_6194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49127 (s : N.State) (i : N.Inputs) :
  R.v49127 (state s) (inputs i) = Zmod.unsigned (N.v49127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49127 s i)) at 1.
  unfold R.v49127, N.v49127.
  unfold R.v6, N.v6.
  rewrite ?node_6190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49128 (s : N.State) (i : N.Inputs) :
  R.v49128 (state s) (inputs i) = Zmod.unsigned (N.v49128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49128 s i)) at 1.
  unfold R.v49128, N.v49128.
  unfold R.v6, N.v6.
  rewrite ?node_6171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49129 (s : N.State) (i : N.Inputs) :
  R.v49129 (state s) (inputs i) = Zmod.unsigned (N.v49129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49129 s i)) at 1.
  unfold R.v49129, N.v49129.
  rewrite ?node_49127.
  rewrite ?node_49128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49130 (s : N.State) (i : N.Inputs) :
  R.v49130 (state s) (inputs i) = Zmod.unsigned (N.v49130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49130 s i)) at 1.
  unfold R.v49130, N.v49130.
  unfold R.v16484, N.v16484.
  rewrite ?node_49129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49131 (s : N.State) (i : N.Inputs) :
  R.v49131 (state s) (inputs i) = Zmod.unsigned (N.v49131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49131 s i)) at 1.
  unfold R.v49131, N.v49131.
  rewrite ?node_49124.
  rewrite ?node_49125.
  rewrite ?node_49126.
  rewrite ?node_49130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49132 (s : N.State) (i : N.Inputs) :
  R.v49132 (state s) (inputs i) = Zmod.unsigned (N.v49132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49132 s i)) at 1.
  unfold R.v49132, N.v49132.
  unfold R.v6, N.v6.
  rewrite ?node_49131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49133 (s : N.State) (i : N.Inputs) :
  R.v49133 (state s) (inputs i) = Zmod.unsigned (N.v49133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49133 s i)) at 1.
  unfold R.v49133, N.v49133.
  rewrite ?node_6203.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49134 (s : N.State) (i : N.Inputs) :
  R.v49134 (state s) (inputs i) = Zmod.unsigned (N.v49134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49134 s i)) at 1.
  unfold R.v49134, N.v49134.
  unfold R.v6, N.v6.
  rewrite ?node_6276.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49135 (s : N.State) (i : N.Inputs) :
  R.v49135 (state s) (inputs i) = Zmod.unsigned (N.v49135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49135 s i)) at 1.
  unfold R.v49135, N.v49135.
  unfold R.v6, N.v6.
  rewrite ?node_6280.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49136 (s : N.State) (i : N.Inputs) :
  R.v49136 (state s) (inputs i) = Zmod.unsigned (N.v49136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49136 s i)) at 1.
  unfold R.v49136, N.v49136.
  rewrite ?node_49133.
  rewrite ?node_49134.
  rewrite ?node_49135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49137 (s : N.State) (i : N.Inputs) :
  R.v49137 (state s) (inputs i) = Zmod.unsigned (N.v49137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49137 s i)) at 1.
  unfold R.v49137, N.v49137.
  rewrite ?node_49132.
  rewrite ?node_49136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49138 (s : N.State) (i : N.Inputs) :
  R.v49138 (state s) (inputs i) = Zmod.unsigned (N.v49138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49138 s i)) at 1.
  unfold R.v49138, N.v49138.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49139 (s : N.State) (i : N.Inputs) :
  R.v49139 (state s) (inputs i) = Zmod.unsigned (N.v49139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49139 s i)) at 1.
  unfold R.v49139, N.v49139.
  rewrite ?node_6194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49140 (s : N.State) (i : N.Inputs) :
  R.v49140 (state s) (inputs i) = Zmod.unsigned (N.v49140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49140 s i)) at 1.
  unfold R.v49140, N.v49140.
  unfold R.v6, N.v6.
  rewrite ?node_6190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49141 (s : N.State) (i : N.Inputs) :
  R.v49141 (state s) (inputs i) = Zmod.unsigned (N.v49141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49141 s i)) at 1.
  unfold R.v49141, N.v49141.
  unfold R.v6, N.v6.
  rewrite ?node_6171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49142 (s : N.State) (i : N.Inputs) :
  R.v49142 (state s) (inputs i) = Zmod.unsigned (N.v49142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49142 s i)) at 1.
  unfold R.v49142, N.v49142.
  rewrite ?node_49140.
  rewrite ?node_49141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49143 (s : N.State) (i : N.Inputs) :
  R.v49143 (state s) (inputs i) = Zmod.unsigned (N.v49143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49143 s i)) at 1.
  unfold R.v49143, N.v49143.
  unfold R.v16484, N.v16484.
  rewrite ?node_49142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49144 (s : N.State) (i : N.Inputs) :
  R.v49144 (state s) (inputs i) = Zmod.unsigned (N.v49144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49144 s i)) at 1.
  unfold R.v49144, N.v49144.
  rewrite ?node_49139.
  rewrite ?node_49143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49145 (s : N.State) (i : N.Inputs) :
  R.v49145 (state s) (inputs i) = Zmod.unsigned (N.v49145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49145 s i)) at 1.
  unfold R.v49145, N.v49145.
  unfold R.v6, N.v6.
  rewrite ?node_49144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49146 (s : N.State) (i : N.Inputs) :
  R.v49146 (state s) (inputs i) = Zmod.unsigned (N.v49146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49146 s i)) at 1.
  unfold R.v49146, N.v49146.
  rewrite ?node_6195.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49147 (s : N.State) (i : N.Inputs) :
  R.v49147 (state s) (inputs i) = Zmod.unsigned (N.v49147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49147 s i)) at 1.
  unfold R.v49147, N.v49147.
  unfold R.v6, N.v6.
  rewrite ?node_6276.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49148 (s : N.State) (i : N.Inputs) :
  R.v49148 (state s) (inputs i) = Zmod.unsigned (N.v49148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49148 s i)) at 1.
  unfold R.v49148, N.v49148.
  rewrite ?node_49146.
  rewrite ?node_49147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49149 (s : N.State) (i : N.Inputs) :
  R.v49149 (state s) (inputs i) = Zmod.unsigned (N.v49149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49149 s i)) at 1.
  unfold R.v49149, N.v49149.
  rewrite ?node_49145.
  rewrite ?node_49148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49150 (s : N.State) (i : N.Inputs) :
  R.v49150 (state s) (inputs i) = Zmod.unsigned (N.v49150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49150 s i)) at 1.
  unfold R.v49150, N.v49150.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49151 (s : N.State) (i : N.Inputs) :
  R.v49151 (state s) (inputs i) = Zmod.unsigned (N.v49151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49151 s i)) at 1.
  unfold R.v49151, N.v49151.
  rewrite ?node_6202.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49152 (s : N.State) (i : N.Inputs) :
  R.v49152 (state s) (inputs i) = Zmod.unsigned (N.v49152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49152 s i)) at 1.
  unfold R.v49152, N.v49152.
  unfold R.v6, N.v6.
  rewrite ?node_6198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49153 (s : N.State) (i : N.Inputs) :
  R.v49153 (state s) (inputs i) = Zmod.unsigned (N.v49153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49153 s i)) at 1.
  unfold R.v49153, N.v49153.
  unfold R.v6, N.v6.
  rewrite ?node_6195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49154 (s : N.State) (i : N.Inputs) :
  R.v49154 (state s) (inputs i) = Zmod.unsigned (N.v49154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49154 s i)) at 1.
  unfold R.v49154, N.v49154.
  rewrite ?node_49152.
  rewrite ?node_49153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49155 (s : N.State) (i : N.Inputs) :
  R.v49155 (state s) (inputs i) = Zmod.unsigned (N.v49155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49155 s i)) at 1.
  unfold R.v49155, N.v49155.
  unfold R.v16484, N.v16484.
  rewrite ?node_49154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49156 (s : N.State) (i : N.Inputs) :
  R.v49156 (state s) (inputs i) = Zmod.unsigned (N.v49156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49156 s i)) at 1.
  unfold R.v49156, N.v49156.
  rewrite ?node_49151.
  rewrite ?node_49155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49157 (s : N.State) (i : N.Inputs) :
  R.v49157 (state s) (inputs i) = Zmod.unsigned (N.v49157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49157 s i)) at 1.
  unfold R.v49157, N.v49157.
  unfold R.v6, N.v6.
  rewrite ?node_49156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49158 (s : N.State) (i : N.Inputs) :
  R.v49158 (state s) (inputs i) = Zmod.unsigned (N.v49158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49158 s i)) at 1.
  unfold R.v49158, N.v49158.
  rewrite ?node_6203.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49159 (s : N.State) (i : N.Inputs) :
  R.v49159 (state s) (inputs i) = Zmod.unsigned (N.v49159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49159 s i)) at 1.
  unfold R.v49159, N.v49159.
  unfold R.v6, N.v6.
  rewrite ?node_6280.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49160 (s : N.State) (i : N.Inputs) :
  R.v49160 (state s) (inputs i) = Zmod.unsigned (N.v49160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49160 s i)) at 1.
  unfold R.v49160, N.v49160.
  rewrite ?node_49158.
  rewrite ?node_49159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49161 (s : N.State) (i : N.Inputs) :
  R.v49161 (state s) (inputs i) = Zmod.unsigned (N.v49161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49161 s i)) at 1.
  unfold R.v49161, N.v49161.
  rewrite ?node_49157.
  rewrite ?node_49160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49162 (s : N.State) (i : N.Inputs) :
  R.v49162 (state s) (inputs i) = Zmod.unsigned (N.v49162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49162 s i)) at 1.
  unfold R.v49162, N.v49162.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49163 (s : N.State) (i : N.Inputs) :
  R.v49163 (state s) (inputs i) = Zmod.unsigned (N.v49163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49163 s i)) at 1.
  unfold R.v49163, N.v49163.
  rewrite ?node_6276.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49164 (s : N.State) (i : N.Inputs) :
  R.v49164 (state s) (inputs i) = Zmod.unsigned (N.v49164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49164 s i)) at 1.
  unfold R.v49164, N.v49164.
  rewrite ?node_6272.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49165 (s : N.State) (i : N.Inputs) :
  R.v49165 (state s) (inputs i) = Zmod.unsigned (N.v49165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49165 s i)) at 1.
  unfold R.v49165, N.v49165.
  rewrite ?node_6268.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49166 (s : N.State) (i : N.Inputs) :
  R.v49166 (state s) (inputs i) = Zmod.unsigned (N.v49166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49166 s i)) at 1.
  unfold R.v49166, N.v49166.
  unfold R.v6, N.v6.
  rewrite ?node_6264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49167 (s : N.State) (i : N.Inputs) :
  R.v49167 (state s) (inputs i) = Zmod.unsigned (N.v49167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49167 s i)) at 1.
  unfold R.v49167, N.v49167.
  unfold R.v6, N.v6.
  rewrite ?node_6247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49168 (s : N.State) (i : N.Inputs) :
  R.v49168 (state s) (inputs i) = Zmod.unsigned (N.v49168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49168 s i)) at 1.
  unfold R.v49168, N.v49168.
  rewrite ?node_49166.
  rewrite ?node_49167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49169 (s : N.State) (i : N.Inputs) :
  R.v49169 (state s) (inputs i) = Zmod.unsigned (N.v49169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49169 s i)) at 1.
  unfold R.v49169, N.v49169.
  unfold R.v16484, N.v16484.
  rewrite ?node_49168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49170 (s : N.State) (i : N.Inputs) :
  R.v49170 (state s) (inputs i) = Zmod.unsigned (N.v49170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49170 s i)) at 1.
  unfold R.v49170, N.v49170.
  rewrite ?node_49163.
  rewrite ?node_49164.
  rewrite ?node_49165.
  rewrite ?node_49169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49171 (s : N.State) (i : N.Inputs) :
  R.v49171 (state s) (inputs i) = Zmod.unsigned (N.v49171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49171 s i)) at 1.
  unfold R.v49171, N.v49171.
  unfold R.v6, N.v6.
  rewrite ?node_49170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49172 (s : N.State) (i : N.Inputs) :
  R.v49172 (state s) (inputs i) = Zmod.unsigned (N.v49172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49172 s i)) at 1.
  unfold R.v49172, N.v49172.
  rewrite ?node_6277.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49173 (s : N.State) (i : N.Inputs) :
  R.v49173 (state s) (inputs i) = Zmod.unsigned (N.v49173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49173 s i)) at 1.
  unfold R.v49173, N.v49173.
  unfold R.v6, N.v6.
  rewrite ?node_6349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49174 (s : N.State) (i : N.Inputs) :
  R.v49174 (state s) (inputs i) = Zmod.unsigned (N.v49174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49174 s i)) at 1.
  unfold R.v49174, N.v49174.
  unfold R.v6, N.v6.
  rewrite ?node_6357.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49175 (s : N.State) (i : N.Inputs) :
  R.v49175 (state s) (inputs i) = Zmod.unsigned (N.v49175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49175 s i)) at 1.
  unfold R.v49175, N.v49175.
  rewrite ?node_49172.
  rewrite ?node_49173.
  rewrite ?node_49174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49176 (s : N.State) (i : N.Inputs) :
  R.v49176 (state s) (inputs i) = Zmod.unsigned (N.v49176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49176 s i)) at 1.
  unfold R.v49176, N.v49176.
  rewrite ?node_49171.
  rewrite ?node_49175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49177 (s : N.State) (i : N.Inputs) :
  R.v49177 (state s) (inputs i) = Zmod.unsigned (N.v49177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49177 s i)) at 1.
  unfold R.v49177, N.v49177.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49178 (s : N.State) (i : N.Inputs) :
  R.v49178 (state s) (inputs i) = Zmod.unsigned (N.v49178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49178 s i)) at 1.
  unfold R.v49178, N.v49178.
  rewrite ?node_6268.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49179 (s : N.State) (i : N.Inputs) :
  R.v49179 (state s) (inputs i) = Zmod.unsigned (N.v49179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49179 s i)) at 1.
  unfold R.v49179, N.v49179.
  unfold R.v6, N.v6.
  rewrite ?node_6264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49180 (s : N.State) (i : N.Inputs) :
  R.v49180 (state s) (inputs i) = Zmod.unsigned (N.v49180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49180 s i)) at 1.
  unfold R.v49180, N.v49180.
  unfold R.v6, N.v6.
  rewrite ?node_6247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49181 (s : N.State) (i : N.Inputs) :
  R.v49181 (state s) (inputs i) = Zmod.unsigned (N.v49181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49181 s i)) at 1.
  unfold R.v49181, N.v49181.
  rewrite ?node_49179.
  rewrite ?node_49180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49182 (s : N.State) (i : N.Inputs) :
  R.v49182 (state s) (inputs i) = Zmod.unsigned (N.v49182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49182 s i)) at 1.
  unfold R.v49182, N.v49182.
  unfold R.v16484, N.v16484.
  rewrite ?node_49181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49183 (s : N.State) (i : N.Inputs) :
  R.v49183 (state s) (inputs i) = Zmod.unsigned (N.v49183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49183 s i)) at 1.
  unfold R.v49183, N.v49183.
  rewrite ?node_49178.
  rewrite ?node_49182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49184 (s : N.State) (i : N.Inputs) :
  R.v49184 (state s) (inputs i) = Zmod.unsigned (N.v49184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49184 s i)) at 1.
  unfold R.v49184, N.v49184.
  unfold R.v6, N.v6.
  rewrite ?node_49183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49185 (s : N.State) (i : N.Inputs) :
  R.v49185 (state s) (inputs i) = Zmod.unsigned (N.v49185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49185 s i)) at 1.
  unfold R.v49185, N.v49185.
  rewrite ?node_6269.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49186 (s : N.State) (i : N.Inputs) :
  R.v49186 (state s) (inputs i) = Zmod.unsigned (N.v49186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49186 s i)) at 1.
  unfold R.v49186, N.v49186.
  unfold R.v6, N.v6.
  rewrite ?node_6349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49187 (s : N.State) (i : N.Inputs) :
  R.v49187 (state s) (inputs i) = Zmod.unsigned (N.v49187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49187 s i)) at 1.
  unfold R.v49187, N.v49187.
  rewrite ?node_49185.
  rewrite ?node_49186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49188 (s : N.State) (i : N.Inputs) :
  R.v49188 (state s) (inputs i) = Zmod.unsigned (N.v49188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49188 s i)) at 1.
  unfold R.v49188, N.v49188.
  rewrite ?node_49184.
  rewrite ?node_49187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49189 (s : N.State) (i : N.Inputs) :
  R.v49189 (state s) (inputs i) = Zmod.unsigned (N.v49189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49189 s i)) at 1.
  unfold R.v49189, N.v49189.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49190 (s : N.State) (i : N.Inputs) :
  R.v49190 (state s) (inputs i) = Zmod.unsigned (N.v49190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49190 s i)) at 1.
  unfold R.v49190, N.v49190.
  rewrite ?node_6276.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49191 (s : N.State) (i : N.Inputs) :
  R.v49191 (state s) (inputs i) = Zmod.unsigned (N.v49191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49191 s i)) at 1.
  unfold R.v49191, N.v49191.
  unfold R.v6, N.v6.
  rewrite ?node_6272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49192 (s : N.State) (i : N.Inputs) :
  R.v49192 (state s) (inputs i) = Zmod.unsigned (N.v49192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49192 s i)) at 1.
  unfold R.v49192, N.v49192.
  unfold R.v6, N.v6.
  rewrite ?node_6269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49193 (s : N.State) (i : N.Inputs) :
  R.v49193 (state s) (inputs i) = Zmod.unsigned (N.v49193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49193 s i)) at 1.
  unfold R.v49193, N.v49193.
  rewrite ?node_49191.
  rewrite ?node_49192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49194 (s : N.State) (i : N.Inputs) :
  R.v49194 (state s) (inputs i) = Zmod.unsigned (N.v49194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49194 s i)) at 1.
  unfold R.v49194, N.v49194.
  unfold R.v16484, N.v16484.
  rewrite ?node_49193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49195 (s : N.State) (i : N.Inputs) :
  R.v49195 (state s) (inputs i) = Zmod.unsigned (N.v49195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49195 s i)) at 1.
  unfold R.v49195, N.v49195.
  rewrite ?node_49190.
  rewrite ?node_49194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49196 (s : N.State) (i : N.Inputs) :
  R.v49196 (state s) (inputs i) = Zmod.unsigned (N.v49196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49196 s i)) at 1.
  unfold R.v49196, N.v49196.
  unfold R.v6, N.v6.
  rewrite ?node_49195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49197 (s : N.State) (i : N.Inputs) :
  R.v49197 (state s) (inputs i) = Zmod.unsigned (N.v49197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49197 s i)) at 1.
  unfold R.v49197, N.v49197.
  rewrite ?node_6277.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49198 (s : N.State) (i : N.Inputs) :
  R.v49198 (state s) (inputs i) = Zmod.unsigned (N.v49198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49198 s i)) at 1.
  unfold R.v49198, N.v49198.
  unfold R.v6, N.v6.
  rewrite ?node_6357.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49199 (s : N.State) (i : N.Inputs) :
  R.v49199 (state s) (inputs i) = Zmod.unsigned (N.v49199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49199 s i)) at 1.
  unfold R.v49199, N.v49199.
  rewrite ?node_49197.
  rewrite ?node_49198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49200 (s : N.State) (i : N.Inputs) :
  R.v49200 (state s) (inputs i) = Zmod.unsigned (N.v49200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49200 s i)) at 1.
  unfold R.v49200, N.v49200.
  rewrite ?node_49196.
  rewrite ?node_49199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49201 (s : N.State) (i : N.Inputs) :
  R.v49201 (state s) (inputs i) = Zmod.unsigned (N.v49201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49201 s i)) at 1.
  unfold R.v49201, N.v49201.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49202 (s : N.State) (i : N.Inputs) :
  R.v49202 (state s) (inputs i) = Zmod.unsigned (N.v49202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49202 s i)) at 1.
  unfold R.v49202, N.v49202.
  rewrite ?node_6349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49203 (s : N.State) (i : N.Inputs) :
  R.v49203 (state s) (inputs i) = Zmod.unsigned (N.v49203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49203 s i)) at 1.
  unfold R.v49203, N.v49203.
  rewrite ?node_6345.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49204 (s : N.State) (i : N.Inputs) :
  R.v49204 (state s) (inputs i) = Zmod.unsigned (N.v49204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49204 s i)) at 1.
  unfold R.v49204, N.v49204.
  rewrite ?node_6341.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49205 (s : N.State) (i : N.Inputs) :
  R.v49205 (state s) (inputs i) = Zmod.unsigned (N.v49205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49205 s i)) at 1.
  unfold R.v49205, N.v49205.
  unfold R.v6, N.v6.
  rewrite ?node_6337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49206 (s : N.State) (i : N.Inputs) :
  R.v49206 (state s) (inputs i) = Zmod.unsigned (N.v49206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49206 s i)) at 1.
  unfold R.v49206, N.v49206.
  unfold R.v6, N.v6.
  rewrite ?node_6321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49207 (s : N.State) (i : N.Inputs) :
  R.v49207 (state s) (inputs i) = Zmod.unsigned (N.v49207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49207 s i)) at 1.
  unfold R.v49207, N.v49207.
  rewrite ?node_49205.
  rewrite ?node_49206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49208 (s : N.State) (i : N.Inputs) :
  R.v49208 (state s) (inputs i) = Zmod.unsigned (N.v49208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49208 s i)) at 1.
  unfold R.v49208, N.v49208.
  unfold R.v16484, N.v16484.
  rewrite ?node_49207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49209 (s : N.State) (i : N.Inputs) :
  R.v49209 (state s) (inputs i) = Zmod.unsigned (N.v49209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49209 s i)) at 1.
  unfold R.v49209, N.v49209.
  rewrite ?node_49202.
  rewrite ?node_49203.
  rewrite ?node_49204.
  rewrite ?node_49208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49210 (s : N.State) (i : N.Inputs) :
  R.v49210 (state s) (inputs i) = Zmod.unsigned (N.v49210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49210 s i)) at 1.
  unfold R.v49210, N.v49210.
  unfold R.v6, N.v6.
  rewrite ?node_49209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49211 (s : N.State) (i : N.Inputs) :
  R.v49211 (state s) (inputs i) = Zmod.unsigned (N.v49211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49211 s i)) at 1.
  unfold R.v49211, N.v49211.
  rewrite ?node_6350.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49212 (s : N.State) (i : N.Inputs) :
  R.v49212 (state s) (inputs i) = Zmod.unsigned (N.v49212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49212 s i)) at 1.
  unfold R.v49212, N.v49212.
  unfold R.v6, N.v6.
  rewrite ?node_6426.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49213 (s : N.State) (i : N.Inputs) :
  R.v49213 (state s) (inputs i) = Zmod.unsigned (N.v49213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49213 s i)) at 1.
  unfold R.v49213, N.v49213.
  unfold R.v6, N.v6.
  rewrite ?node_6434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49214 (s : N.State) (i : N.Inputs) :
  R.v49214 (state s) (inputs i) = Zmod.unsigned (N.v49214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49214 s i)) at 1.
  unfold R.v49214, N.v49214.
  rewrite ?node_49211.
  rewrite ?node_49212.
  rewrite ?node_49213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49215 (s : N.State) (i : N.Inputs) :
  R.v49215 (state s) (inputs i) = Zmod.unsigned (N.v49215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49215 s i)) at 1.
  unfold R.v49215, N.v49215.
  rewrite ?node_49210.
  rewrite ?node_49214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49216 (s : N.State) (i : N.Inputs) :
  R.v49216 (state s) (inputs i) = Zmod.unsigned (N.v49216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49216 s i)) at 1.
  unfold R.v49216, N.v49216.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49217 (s : N.State) (i : N.Inputs) :
  R.v49217 (state s) (inputs i) = Zmod.unsigned (N.v49217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49217 s i)) at 1.
  unfold R.v49217, N.v49217.
  rewrite ?node_6341.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49218 (s : N.State) (i : N.Inputs) :
  R.v49218 (state s) (inputs i) = Zmod.unsigned (N.v49218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49218 s i)) at 1.
  unfold R.v49218, N.v49218.
  unfold R.v6, N.v6.
  rewrite ?node_6337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49219 (s : N.State) (i : N.Inputs) :
  R.v49219 (state s) (inputs i) = Zmod.unsigned (N.v49219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49219 s i)) at 1.
  unfold R.v49219, N.v49219.
  unfold R.v6, N.v6.
  rewrite ?node_6321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49220 (s : N.State) (i : N.Inputs) :
  R.v49220 (state s) (inputs i) = Zmod.unsigned (N.v49220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49220 s i)) at 1.
  unfold R.v49220, N.v49220.
  rewrite ?node_49218.
  rewrite ?node_49219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49221 (s : N.State) (i : N.Inputs) :
  R.v49221 (state s) (inputs i) = Zmod.unsigned (N.v49221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49221 s i)) at 1.
  unfold R.v49221, N.v49221.
  unfold R.v16484, N.v16484.
  rewrite ?node_49220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49222 (s : N.State) (i : N.Inputs) :
  R.v49222 (state s) (inputs i) = Zmod.unsigned (N.v49222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49222 s i)) at 1.
  unfold R.v49222, N.v49222.
  rewrite ?node_49217.
  rewrite ?node_49221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49223 (s : N.State) (i : N.Inputs) :
  R.v49223 (state s) (inputs i) = Zmod.unsigned (N.v49223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49223 s i)) at 1.
  unfold R.v49223, N.v49223.
  unfold R.v6, N.v6.
  rewrite ?node_49222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49224 (s : N.State) (i : N.Inputs) :
  R.v49224 (state s) (inputs i) = Zmod.unsigned (N.v49224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49224 s i)) at 1.
  unfold R.v49224, N.v49224.
  rewrite ?node_6342.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49225 (s : N.State) (i : N.Inputs) :
  R.v49225 (state s) (inputs i) = Zmod.unsigned (N.v49225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49225 s i)) at 1.
  unfold R.v49225, N.v49225.
  unfold R.v6, N.v6.
  rewrite ?node_6426.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49226 (s : N.State) (i : N.Inputs) :
  R.v49226 (state s) (inputs i) = Zmod.unsigned (N.v49226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49226 s i)) at 1.
  unfold R.v49226, N.v49226.
  rewrite ?node_49224.
  rewrite ?node_49225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49227 (s : N.State) (i : N.Inputs) :
  R.v49227 (state s) (inputs i) = Zmod.unsigned (N.v49227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49227 s i)) at 1.
  unfold R.v49227, N.v49227.
  rewrite ?node_49223.
  rewrite ?node_49226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49228 (s : N.State) (i : N.Inputs) :
  R.v49228 (state s) (inputs i) = Zmod.unsigned (N.v49228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49228 s i)) at 1.
  unfold R.v49228, N.v49228.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49229 (s : N.State) (i : N.Inputs) :
  R.v49229 (state s) (inputs i) = Zmod.unsigned (N.v49229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49229 s i)) at 1.
  unfold R.v49229, N.v49229.
  rewrite ?node_6349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49230 (s : N.State) (i : N.Inputs) :
  R.v49230 (state s) (inputs i) = Zmod.unsigned (N.v49230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49230 s i)) at 1.
  unfold R.v49230, N.v49230.
  unfold R.v6, N.v6.
  rewrite ?node_6345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49231 (s : N.State) (i : N.Inputs) :
  R.v49231 (state s) (inputs i) = Zmod.unsigned (N.v49231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49231 s i)) at 1.
  unfold R.v49231, N.v49231.
  unfold R.v6, N.v6.
  rewrite ?node_6342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49232 (s : N.State) (i : N.Inputs) :
  R.v49232 (state s) (inputs i) = Zmod.unsigned (N.v49232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49232 s i)) at 1.
  unfold R.v49232, N.v49232.
  rewrite ?node_49230.
  rewrite ?node_49231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49233 (s : N.State) (i : N.Inputs) :
  R.v49233 (state s) (inputs i) = Zmod.unsigned (N.v49233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49233 s i)) at 1.
  unfold R.v49233, N.v49233.
  unfold R.v16484, N.v16484.
  rewrite ?node_49232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49234 (s : N.State) (i : N.Inputs) :
  R.v49234 (state s) (inputs i) = Zmod.unsigned (N.v49234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49234 s i)) at 1.
  unfold R.v49234, N.v49234.
  rewrite ?node_49229.
  rewrite ?node_49233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49235 (s : N.State) (i : N.Inputs) :
  R.v49235 (state s) (inputs i) = Zmod.unsigned (N.v49235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49235 s i)) at 1.
  unfold R.v49235, N.v49235.
  unfold R.v6, N.v6.
  rewrite ?node_49234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49236 (s : N.State) (i : N.Inputs) :
  R.v49236 (state s) (inputs i) = Zmod.unsigned (N.v49236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49236 s i)) at 1.
  unfold R.v49236, N.v49236.
  rewrite ?node_6350.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49237 (s : N.State) (i : N.Inputs) :
  R.v49237 (state s) (inputs i) = Zmod.unsigned (N.v49237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49237 s i)) at 1.
  unfold R.v49237, N.v49237.
  unfold R.v6, N.v6.
  rewrite ?node_6434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49238 (s : N.State) (i : N.Inputs) :
  R.v49238 (state s) (inputs i) = Zmod.unsigned (N.v49238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49238 s i)) at 1.
  unfold R.v49238, N.v49238.
  rewrite ?node_49236.
  rewrite ?node_49237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49239 (s : N.State) (i : N.Inputs) :
  R.v49239 (state s) (inputs i) = Zmod.unsigned (N.v49239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49239 s i)) at 1.
  unfold R.v49239, N.v49239.
  rewrite ?node_49235.
  rewrite ?node_49238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49240 (s : N.State) (i : N.Inputs) :
  R.v49240 (state s) (inputs i) = Zmod.unsigned (N.v49240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49240 s i)) at 1.
  unfold R.v49240, N.v49240.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49241 (s : N.State) (i : N.Inputs) :
  R.v49241 (state s) (inputs i) = Zmod.unsigned (N.v49241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49241 s i)) at 1.
  unfold R.v49241, N.v49241.
  rewrite ?node_6426.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49242 (s : N.State) (i : N.Inputs) :
  R.v49242 (state s) (inputs i) = Zmod.unsigned (N.v49242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49242 s i)) at 1.
  unfold R.v49242, N.v49242.
  rewrite ?node_6422.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49243 (s : N.State) (i : N.Inputs) :
  R.v49243 (state s) (inputs i) = Zmod.unsigned (N.v49243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49243 s i)) at 1.
  unfold R.v49243, N.v49243.
  rewrite ?node_6418.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49244 (s : N.State) (i : N.Inputs) :
  R.v49244 (state s) (inputs i) = Zmod.unsigned (N.v49244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49244 s i)) at 1.
  unfold R.v49244, N.v49244.
  unfold R.v6, N.v6.
  rewrite ?node_6414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49245 (s : N.State) (i : N.Inputs) :
  R.v49245 (state s) (inputs i) = Zmod.unsigned (N.v49245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49245 s i)) at 1.
  unfold R.v49245, N.v49245.
  unfold R.v6, N.v6.
  rewrite ?node_6398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49246 (s : N.State) (i : N.Inputs) :
  R.v49246 (state s) (inputs i) = Zmod.unsigned (N.v49246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49246 s i)) at 1.
  unfold R.v49246, N.v49246.
  rewrite ?node_49244.
  rewrite ?node_49245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49247 (s : N.State) (i : N.Inputs) :
  R.v49247 (state s) (inputs i) = Zmod.unsigned (N.v49247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49247 s i)) at 1.
  unfold R.v49247, N.v49247.
  unfold R.v16484, N.v16484.
  rewrite ?node_49246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49248 (s : N.State) (i : N.Inputs) :
  R.v49248 (state s) (inputs i) = Zmod.unsigned (N.v49248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49248 s i)) at 1.
  unfold R.v49248, N.v49248.
  rewrite ?node_49241.
  rewrite ?node_49242.
  rewrite ?node_49243.
  rewrite ?node_49247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49249 (s : N.State) (i : N.Inputs) :
  R.v49249 (state s) (inputs i) = Zmod.unsigned (N.v49249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49249 s i)) at 1.
  unfold R.v49249, N.v49249.
  unfold R.v6, N.v6.
  rewrite ?node_49248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49250 (s : N.State) (i : N.Inputs) :
  R.v49250 (state s) (inputs i) = Zmod.unsigned (N.v49250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49250 s i)) at 1.
  unfold R.v49250, N.v49250.
  rewrite ?node_6427.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49251 (s : N.State) (i : N.Inputs) :
  R.v49251 (state s) (inputs i) = Zmod.unsigned (N.v49251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49251 s i)) at 1.
  unfold R.v49251, N.v49251.
  unfold R.v6, N.v6.
  rewrite ?node_6506.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49252 (s : N.State) (i : N.Inputs) :
  R.v49252 (state s) (inputs i) = Zmod.unsigned (N.v49252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49252 s i)) at 1.
  unfold R.v49252, N.v49252.
  unfold R.v6, N.v6.
  rewrite ?node_6514.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49253 (s : N.State) (i : N.Inputs) :
  R.v49253 (state s) (inputs i) = Zmod.unsigned (N.v49253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49253 s i)) at 1.
  unfold R.v49253, N.v49253.
  rewrite ?node_49250.
  rewrite ?node_49251.
  rewrite ?node_49252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49254 (s : N.State) (i : N.Inputs) :
  R.v49254 (state s) (inputs i) = Zmod.unsigned (N.v49254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49254 s i)) at 1.
  unfold R.v49254, N.v49254.
  rewrite ?node_49249.
  rewrite ?node_49253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49255 (s : N.State) (i : N.Inputs) :
  R.v49255 (state s) (inputs i) = Zmod.unsigned (N.v49255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49255 s i)) at 1.
  unfold R.v49255, N.v49255.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49256 (s : N.State) (i : N.Inputs) :
  R.v49256 (state s) (inputs i) = Zmod.unsigned (N.v49256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49256 s i)) at 1.
  unfold R.v49256, N.v49256.
  rewrite ?node_6418.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49257 (s : N.State) (i : N.Inputs) :
  R.v49257 (state s) (inputs i) = Zmod.unsigned (N.v49257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49257 s i)) at 1.
  unfold R.v49257, N.v49257.
  unfold R.v6, N.v6.
  rewrite ?node_6414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49258 (s : N.State) (i : N.Inputs) :
  R.v49258 (state s) (inputs i) = Zmod.unsigned (N.v49258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49258 s i)) at 1.
  unfold R.v49258, N.v49258.
  unfold R.v6, N.v6.
  rewrite ?node_6398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49259 (s : N.State) (i : N.Inputs) :
  R.v49259 (state s) (inputs i) = Zmod.unsigned (N.v49259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49259 s i)) at 1.
  unfold R.v49259, N.v49259.
  rewrite ?node_49257.
  rewrite ?node_49258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49260 (s : N.State) (i : N.Inputs) :
  R.v49260 (state s) (inputs i) = Zmod.unsigned (N.v49260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49260 s i)) at 1.
  unfold R.v49260, N.v49260.
  unfold R.v16484, N.v16484.
  rewrite ?node_49259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49261 (s : N.State) (i : N.Inputs) :
  R.v49261 (state s) (inputs i) = Zmod.unsigned (N.v49261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49261 s i)) at 1.
  unfold R.v49261, N.v49261.
  rewrite ?node_49256.
  rewrite ?node_49260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49262 (s : N.State) (i : N.Inputs) :
  R.v49262 (state s) (inputs i) = Zmod.unsigned (N.v49262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49262 s i)) at 1.
  unfold R.v49262, N.v49262.
  unfold R.v6, N.v6.
  rewrite ?node_49261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49263 (s : N.State) (i : N.Inputs) :
  R.v49263 (state s) (inputs i) = Zmod.unsigned (N.v49263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49263 s i)) at 1.
  unfold R.v49263, N.v49263.
  rewrite ?node_6419.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49264 (s : N.State) (i : N.Inputs) :
  R.v49264 (state s) (inputs i) = Zmod.unsigned (N.v49264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49264 s i)) at 1.
  unfold R.v49264, N.v49264.
  unfold R.v6, N.v6.
  rewrite ?node_6506.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49265 (s : N.State) (i : N.Inputs) :
  R.v49265 (state s) (inputs i) = Zmod.unsigned (N.v49265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49265 s i)) at 1.
  unfold R.v49265, N.v49265.
  rewrite ?node_49263.
  rewrite ?node_49264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49266 (s : N.State) (i : N.Inputs) :
  R.v49266 (state s) (inputs i) = Zmod.unsigned (N.v49266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49266 s i)) at 1.
  unfold R.v49266, N.v49266.
  rewrite ?node_49262.
  rewrite ?node_49265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49267 (s : N.State) (i : N.Inputs) :
  R.v49267 (state s) (inputs i) = Zmod.unsigned (N.v49267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49267 s i)) at 1.
  unfold R.v49267, N.v49267.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49268 (s : N.State) (i : N.Inputs) :
  R.v49268 (state s) (inputs i) = Zmod.unsigned (N.v49268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49268 s i)) at 1.
  unfold R.v49268, N.v49268.
  rewrite ?node_6426.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49269 (s : N.State) (i : N.Inputs) :
  R.v49269 (state s) (inputs i) = Zmod.unsigned (N.v49269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49269 s i)) at 1.
  unfold R.v49269, N.v49269.
  unfold R.v6, N.v6.
  rewrite ?node_6422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49270 (s : N.State) (i : N.Inputs) :
  R.v49270 (state s) (inputs i) = Zmod.unsigned (N.v49270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49270 s i)) at 1.
  unfold R.v49270, N.v49270.
  unfold R.v6, N.v6.
  rewrite ?node_6419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49271 (s : N.State) (i : N.Inputs) :
  R.v49271 (state s) (inputs i) = Zmod.unsigned (N.v49271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49271 s i)) at 1.
  unfold R.v49271, N.v49271.
  rewrite ?node_49269.
  rewrite ?node_49270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49272 (s : N.State) (i : N.Inputs) :
  R.v49272 (state s) (inputs i) = Zmod.unsigned (N.v49272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49272 s i)) at 1.
  unfold R.v49272, N.v49272.
  unfold R.v16484, N.v16484.
  rewrite ?node_49271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49273 (s : N.State) (i : N.Inputs) :
  R.v49273 (state s) (inputs i) = Zmod.unsigned (N.v49273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49273 s i)) at 1.
  unfold R.v49273, N.v49273.
  rewrite ?node_49268.
  rewrite ?node_49272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49274 (s : N.State) (i : N.Inputs) :
  R.v49274 (state s) (inputs i) = Zmod.unsigned (N.v49274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49274 s i)) at 1.
  unfold R.v49274, N.v49274.
  unfold R.v6, N.v6.
  rewrite ?node_49273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49275 (s : N.State) (i : N.Inputs) :
  R.v49275 (state s) (inputs i) = Zmod.unsigned (N.v49275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49275 s i)) at 1.
  unfold R.v49275, N.v49275.
  rewrite ?node_6427.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49276 (s : N.State) (i : N.Inputs) :
  R.v49276 (state s) (inputs i) = Zmod.unsigned (N.v49276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49276 s i)) at 1.
  unfold R.v49276, N.v49276.
  unfold R.v6, N.v6.
  rewrite ?node_6514.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49277 (s : N.State) (i : N.Inputs) :
  R.v49277 (state s) (inputs i) = Zmod.unsigned (N.v49277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49277 s i)) at 1.
  unfold R.v49277, N.v49277.
  rewrite ?node_49275.
  rewrite ?node_49276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49278 (s : N.State) (i : N.Inputs) :
  R.v49278 (state s) (inputs i) = Zmod.unsigned (N.v49278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49278 s i)) at 1.
  unfold R.v49278, N.v49278.
  rewrite ?node_49274.
  rewrite ?node_49277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49279 (s : N.State) (i : N.Inputs) :
  R.v49279 (state s) (inputs i) = Zmod.unsigned (N.v49279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49279 s i)) at 1.
  unfold R.v49279, N.v49279.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49280 (s : N.State) (i : N.Inputs) :
  R.v49280 (state s) (inputs i) = Zmod.unsigned (N.v49280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49280 s i)) at 1.
  unfold R.v49280, N.v49280.
  rewrite ?node_6506.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49281 (s : N.State) (i : N.Inputs) :
  R.v49281 (state s) (inputs i) = Zmod.unsigned (N.v49281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49281 s i)) at 1.
  unfold R.v49281, N.v49281.
  rewrite ?node_6502.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49282 (s : N.State) (i : N.Inputs) :
  R.v49282 (state s) (inputs i) = Zmod.unsigned (N.v49282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49282 s i)) at 1.
  unfold R.v49282, N.v49282.
  rewrite ?node_6498.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49283 (s : N.State) (i : N.Inputs) :
  R.v49283 (state s) (inputs i) = Zmod.unsigned (N.v49283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49283 s i)) at 1.
  unfold R.v49283, N.v49283.
  unfold R.v6, N.v6.
  rewrite ?node_6494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49284 (s : N.State) (i : N.Inputs) :
  R.v49284 (state s) (inputs i) = Zmod.unsigned (N.v49284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49284 s i)) at 1.
  unfold R.v49284, N.v49284.
  unfold R.v6, N.v6.
  rewrite ?node_6477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49285 (s : N.State) (i : N.Inputs) :
  R.v49285 (state s) (inputs i) = Zmod.unsigned (N.v49285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49285 s i)) at 1.
  unfold R.v49285, N.v49285.
  rewrite ?node_49283.
  rewrite ?node_49284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49286 (s : N.State) (i : N.Inputs) :
  R.v49286 (state s) (inputs i) = Zmod.unsigned (N.v49286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49286 s i)) at 1.
  unfold R.v49286, N.v49286.
  unfold R.v16484, N.v16484.
  rewrite ?node_49285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49287 (s : N.State) (i : N.Inputs) :
  R.v49287 (state s) (inputs i) = Zmod.unsigned (N.v49287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49287 s i)) at 1.
  unfold R.v49287, N.v49287.
  rewrite ?node_49280.
  rewrite ?node_49281.
  rewrite ?node_49282.
  rewrite ?node_49286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49288 (s : N.State) (i : N.Inputs) :
  R.v49288 (state s) (inputs i) = Zmod.unsigned (N.v49288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49288 s i)) at 1.
  unfold R.v49288, N.v49288.
  unfold R.v6, N.v6.
  rewrite ?node_49287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49289 (s : N.State) (i : N.Inputs) :
  R.v49289 (state s) (inputs i) = Zmod.unsigned (N.v49289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49289 s i)) at 1.
  unfold R.v49289, N.v49289.
  rewrite ?node_6507.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49290 (s : N.State) (i : N.Inputs) :
  R.v49290 (state s) (inputs i) = Zmod.unsigned (N.v49290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49290 s i)) at 1.
  unfold R.v49290, N.v49290.
  unfold R.v6, N.v6.
  rewrite ?node_6588.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49291 (s : N.State) (i : N.Inputs) :
  R.v49291 (state s) (inputs i) = Zmod.unsigned (N.v49291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49291 s i)) at 1.
  unfold R.v49291, N.v49291.
  unfold R.v6, N.v6.
  rewrite ?node_6596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49292 (s : N.State) (i : N.Inputs) :
  R.v49292 (state s) (inputs i) = Zmod.unsigned (N.v49292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49292 s i)) at 1.
  unfold R.v49292, N.v49292.
  rewrite ?node_49289.
  rewrite ?node_49290.
  rewrite ?node_49291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49293 (s : N.State) (i : N.Inputs) :
  R.v49293 (state s) (inputs i) = Zmod.unsigned (N.v49293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49293 s i)) at 1.
  unfold R.v49293, N.v49293.
  rewrite ?node_49288.
  rewrite ?node_49292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49294 (s : N.State) (i : N.Inputs) :
  R.v49294 (state s) (inputs i) = Zmod.unsigned (N.v49294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49294 s i)) at 1.
  unfold R.v49294, N.v49294.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49295 (s : N.State) (i : N.Inputs) :
  R.v49295 (state s) (inputs i) = Zmod.unsigned (N.v49295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49295 s i)) at 1.
  unfold R.v49295, N.v49295.
  rewrite ?node_6498.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49296 (s : N.State) (i : N.Inputs) :
  R.v49296 (state s) (inputs i) = Zmod.unsigned (N.v49296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49296 s i)) at 1.
  unfold R.v49296, N.v49296.
  unfold R.v6, N.v6.
  rewrite ?node_6494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49297 (s : N.State) (i : N.Inputs) :
  R.v49297 (state s) (inputs i) = Zmod.unsigned (N.v49297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49297 s i)) at 1.
  unfold R.v49297, N.v49297.
  unfold R.v6, N.v6.
  rewrite ?node_6477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49298 (s : N.State) (i : N.Inputs) :
  R.v49298 (state s) (inputs i) = Zmod.unsigned (N.v49298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49298 s i)) at 1.
  unfold R.v49298, N.v49298.
  rewrite ?node_49296.
  rewrite ?node_49297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49299 (s : N.State) (i : N.Inputs) :
  R.v49299 (state s) (inputs i) = Zmod.unsigned (N.v49299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49299 s i)) at 1.
  unfold R.v49299, N.v49299.
  unfold R.v16484, N.v16484.
  rewrite ?node_49298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49300 (s : N.State) (i : N.Inputs) :
  R.v49300 (state s) (inputs i) = Zmod.unsigned (N.v49300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49300 s i)) at 1.
  unfold R.v49300, N.v49300.
  rewrite ?node_49295.
  rewrite ?node_49299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49301 (s : N.State) (i : N.Inputs) :
  R.v49301 (state s) (inputs i) = Zmod.unsigned (N.v49301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49301 s i)) at 1.
  unfold R.v49301, N.v49301.
  unfold R.v6, N.v6.
  rewrite ?node_49300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49302 (s : N.State) (i : N.Inputs) :
  R.v49302 (state s) (inputs i) = Zmod.unsigned (N.v49302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49302 s i)) at 1.
  unfold R.v49302, N.v49302.
  rewrite ?node_6499.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49303 (s : N.State) (i : N.Inputs) :
  R.v49303 (state s) (inputs i) = Zmod.unsigned (N.v49303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49303 s i)) at 1.
  unfold R.v49303, N.v49303.
  unfold R.v6, N.v6.
  rewrite ?node_6588.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49304 (s : N.State) (i : N.Inputs) :
  R.v49304 (state s) (inputs i) = Zmod.unsigned (N.v49304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49304 s i)) at 1.
  unfold R.v49304, N.v49304.
  rewrite ?node_49302.
  rewrite ?node_49303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49305 (s : N.State) (i : N.Inputs) :
  R.v49305 (state s) (inputs i) = Zmod.unsigned (N.v49305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49305 s i)) at 1.
  unfold R.v49305, N.v49305.
  rewrite ?node_49301.
  rewrite ?node_49304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49306 (s : N.State) (i : N.Inputs) :
  R.v49306 (state s) (inputs i) = Zmod.unsigned (N.v49306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49306 s i)) at 1.
  unfold R.v49306, N.v49306.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49307 (s : N.State) (i : N.Inputs) :
  R.v49307 (state s) (inputs i) = Zmod.unsigned (N.v49307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49307 s i)) at 1.
  unfold R.v49307, N.v49307.
  rewrite ?node_6506.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49308 (s : N.State) (i : N.Inputs) :
  R.v49308 (state s) (inputs i) = Zmod.unsigned (N.v49308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49308 s i)) at 1.
  unfold R.v49308, N.v49308.
  unfold R.v6, N.v6.
  rewrite ?node_6502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49309 (s : N.State) (i : N.Inputs) :
  R.v49309 (state s) (inputs i) = Zmod.unsigned (N.v49309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49309 s i)) at 1.
  unfold R.v49309, N.v49309.
  unfold R.v6, N.v6.
  rewrite ?node_6499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49310 (s : N.State) (i : N.Inputs) :
  R.v49310 (state s) (inputs i) = Zmod.unsigned (N.v49310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49310 s i)) at 1.
  unfold R.v49310, N.v49310.
  rewrite ?node_49308.
  rewrite ?node_49309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49311 (s : N.State) (i : N.Inputs) :
  R.v49311 (state s) (inputs i) = Zmod.unsigned (N.v49311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49311 s i)) at 1.
  unfold R.v49311, N.v49311.
  unfold R.v16484, N.v16484.
  rewrite ?node_49310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49312 (s : N.State) (i : N.Inputs) :
  R.v49312 (state s) (inputs i) = Zmod.unsigned (N.v49312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49312 s i)) at 1.
  unfold R.v49312, N.v49312.
  rewrite ?node_49307.
  rewrite ?node_49311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49313 (s : N.State) (i : N.Inputs) :
  R.v49313 (state s) (inputs i) = Zmod.unsigned (N.v49313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49313 s i)) at 1.
  unfold R.v49313, N.v49313.
  unfold R.v6, N.v6.
  rewrite ?node_49312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49314 (s : N.State) (i : N.Inputs) :
  R.v49314 (state s) (inputs i) = Zmod.unsigned (N.v49314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49314 s i)) at 1.
  unfold R.v49314, N.v49314.
  rewrite ?node_6507.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49315 (s : N.State) (i : N.Inputs) :
  R.v49315 (state s) (inputs i) = Zmod.unsigned (N.v49315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49315 s i)) at 1.
  unfold R.v49315, N.v49315.
  unfold R.v6, N.v6.
  rewrite ?node_6596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49316 (s : N.State) (i : N.Inputs) :
  R.v49316 (state s) (inputs i) = Zmod.unsigned (N.v49316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49316 s i)) at 1.
  unfold R.v49316, N.v49316.
  rewrite ?node_49314.
  rewrite ?node_49315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49317 (s : N.State) (i : N.Inputs) :
  R.v49317 (state s) (inputs i) = Zmod.unsigned (N.v49317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49317 s i)) at 1.
  unfold R.v49317, N.v49317.
  rewrite ?node_49313.
  rewrite ?node_49316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49318 (s : N.State) (i : N.Inputs) :
  R.v49318 (state s) (inputs i) = Zmod.unsigned (N.v49318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49318 s i)) at 1.
  unfold R.v49318, N.v49318.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49319 (s : N.State) (i : N.Inputs) :
  R.v49319 (state s) (inputs i) = Zmod.unsigned (N.v49319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49319 s i)) at 1.
  unfold R.v49319, N.v49319.
  rewrite ?node_6588.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49320 (s : N.State) (i : N.Inputs) :
  R.v49320 (state s) (inputs i) = Zmod.unsigned (N.v49320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49320 s i)) at 1.
  unfold R.v49320, N.v49320.
  rewrite ?node_6584.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49321 (s : N.State) (i : N.Inputs) :
  R.v49321 (state s) (inputs i) = Zmod.unsigned (N.v49321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49321 s i)) at 1.
  unfold R.v49321, N.v49321.
  rewrite ?node_6580.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49322 (s : N.State) (i : N.Inputs) :
  R.v49322 (state s) (inputs i) = Zmod.unsigned (N.v49322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49322 s i)) at 1.
  unfold R.v49322, N.v49322.
  unfold R.v6, N.v6.
  rewrite ?node_6574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49323 (s : N.State) (i : N.Inputs) :
  R.v49323 (state s) (inputs i) = Zmod.unsigned (N.v49323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49323 s i)) at 1.
  unfold R.v49323, N.v49323.
  unfold R.v6, N.v6.
  rewrite ?node_6557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49324 (s : N.State) (i : N.Inputs) :
  R.v49324 (state s) (inputs i) = Zmod.unsigned (N.v49324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49324 s i)) at 1.
  unfold R.v49324, N.v49324.
  rewrite ?node_49322.
  rewrite ?node_49323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49325 (s : N.State) (i : N.Inputs) :
  R.v49325 (state s) (inputs i) = Zmod.unsigned (N.v49325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49325 s i)) at 1.
  unfold R.v49325, N.v49325.
  unfold R.v16484, N.v16484.
  rewrite ?node_49324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49326 (s : N.State) (i : N.Inputs) :
  R.v49326 (state s) (inputs i) = Zmod.unsigned (N.v49326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49326 s i)) at 1.
  unfold R.v49326, N.v49326.
  rewrite ?node_49319.
  rewrite ?node_49320.
  rewrite ?node_49321.
  rewrite ?node_49325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49327 (s : N.State) (i : N.Inputs) :
  R.v49327 (state s) (inputs i) = Zmod.unsigned (N.v49327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49327 s i)) at 1.
  unfold R.v49327, N.v49327.
  unfold R.v6, N.v6.
  rewrite ?node_49326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49328 (s : N.State) (i : N.Inputs) :
  R.v49328 (state s) (inputs i) = Zmod.unsigned (N.v49328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49328 s i)) at 1.
  unfold R.v49328, N.v49328.
  rewrite ?node_6589.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49329 (s : N.State) (i : N.Inputs) :
  R.v49329 (state s) (inputs i) = Zmod.unsigned (N.v49329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49329 s i)) at 1.
  unfold R.v49329, N.v49329.
  unfold R.v6, N.v6.
  rewrite ?node_6671.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49330 (s : N.State) (i : N.Inputs) :
  R.v49330 (state s) (inputs i) = Zmod.unsigned (N.v49330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49330 s i)) at 1.
  unfold R.v49330, N.v49330.
  unfold R.v6, N.v6.
  rewrite ?node_6681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49331 (s : N.State) (i : N.Inputs) :
  R.v49331 (state s) (inputs i) = Zmod.unsigned (N.v49331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49331 s i)) at 1.
  unfold R.v49331, N.v49331.
  rewrite ?node_49328.
  rewrite ?node_49329.
  rewrite ?node_49330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49332 (s : N.State) (i : N.Inputs) :
  R.v49332 (state s) (inputs i) = Zmod.unsigned (N.v49332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49332 s i)) at 1.
  unfold R.v49332, N.v49332.
  rewrite ?node_49327.
  rewrite ?node_49331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49333 (s : N.State) (i : N.Inputs) :
  R.v49333 (state s) (inputs i) = Zmod.unsigned (N.v49333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49333 s i)) at 1.
  unfold R.v49333, N.v49333.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49334 (s : N.State) (i : N.Inputs) :
  R.v49334 (state s) (inputs i) = Zmod.unsigned (N.v49334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49334 s i)) at 1.
  unfold R.v49334, N.v49334.
  rewrite ?node_6580.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49335 (s : N.State) (i : N.Inputs) :
  R.v49335 (state s) (inputs i) = Zmod.unsigned (N.v49335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49335 s i)) at 1.
  unfold R.v49335, N.v49335.
  unfold R.v6, N.v6.
  rewrite ?node_6574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49336 (s : N.State) (i : N.Inputs) :
  R.v49336 (state s) (inputs i) = Zmod.unsigned (N.v49336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49336 s i)) at 1.
  unfold R.v49336, N.v49336.
  unfold R.v6, N.v6.
  rewrite ?node_6557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49337 (s : N.State) (i : N.Inputs) :
  R.v49337 (state s) (inputs i) = Zmod.unsigned (N.v49337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49337 s i)) at 1.
  unfold R.v49337, N.v49337.
  rewrite ?node_49335.
  rewrite ?node_49336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49338 (s : N.State) (i : N.Inputs) :
  R.v49338 (state s) (inputs i) = Zmod.unsigned (N.v49338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49338 s i)) at 1.
  unfold R.v49338, N.v49338.
  unfold R.v16484, N.v16484.
  rewrite ?node_49337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49339 (s : N.State) (i : N.Inputs) :
  R.v49339 (state s) (inputs i) = Zmod.unsigned (N.v49339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49339 s i)) at 1.
  unfold R.v49339, N.v49339.
  rewrite ?node_49334.
  rewrite ?node_49338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49340 (s : N.State) (i : N.Inputs) :
  R.v49340 (state s) (inputs i) = Zmod.unsigned (N.v49340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49340 s i)) at 1.
  unfold R.v49340, N.v49340.
  unfold R.v6, N.v6.
  rewrite ?node_49339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49341 (s : N.State) (i : N.Inputs) :
  R.v49341 (state s) (inputs i) = Zmod.unsigned (N.v49341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49341 s i)) at 1.
  unfold R.v49341, N.v49341.
  rewrite ?node_6581.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49342 (s : N.State) (i : N.Inputs) :
  R.v49342 (state s) (inputs i) = Zmod.unsigned (N.v49342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49342 s i)) at 1.
  unfold R.v49342, N.v49342.
  unfold R.v6, N.v6.
  rewrite ?node_6671.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49343 (s : N.State) (i : N.Inputs) :
  R.v49343 (state s) (inputs i) = Zmod.unsigned (N.v49343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49343 s i)) at 1.
  unfold R.v49343, N.v49343.
  rewrite ?node_49341.
  rewrite ?node_49342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49344 (s : N.State) (i : N.Inputs) :
  R.v49344 (state s) (inputs i) = Zmod.unsigned (N.v49344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49344 s i)) at 1.
  unfold R.v49344, N.v49344.
  rewrite ?node_49340.
  rewrite ?node_49343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49345 (s : N.State) (i : N.Inputs) :
  R.v49345 (state s) (inputs i) = Zmod.unsigned (N.v49345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49345 s i)) at 1.
  unfold R.v49345, N.v49345.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49346 (s : N.State) (i : N.Inputs) :
  R.v49346 (state s) (inputs i) = Zmod.unsigned (N.v49346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49346 s i)) at 1.
  unfold R.v49346, N.v49346.
  rewrite ?node_6588.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49347 (s : N.State) (i : N.Inputs) :
  R.v49347 (state s) (inputs i) = Zmod.unsigned (N.v49347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49347 s i)) at 1.
  unfold R.v49347, N.v49347.
  unfold R.v6, N.v6.
  rewrite ?node_6584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49348 (s : N.State) (i : N.Inputs) :
  R.v49348 (state s) (inputs i) = Zmod.unsigned (N.v49348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49348 s i)) at 1.
  unfold R.v49348, N.v49348.
  unfold R.v6, N.v6.
  rewrite ?node_6581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49349 (s : N.State) (i : N.Inputs) :
  R.v49349 (state s) (inputs i) = Zmod.unsigned (N.v49349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49349 s i)) at 1.
  unfold R.v49349, N.v49349.
  rewrite ?node_49347.
  rewrite ?node_49348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49350 (s : N.State) (i : N.Inputs) :
  R.v49350 (state s) (inputs i) = Zmod.unsigned (N.v49350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49350 s i)) at 1.
  unfold R.v49350, N.v49350.
  unfold R.v16484, N.v16484.
  rewrite ?node_49349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49351 (s : N.State) (i : N.Inputs) :
  R.v49351 (state s) (inputs i) = Zmod.unsigned (N.v49351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49351 s i)) at 1.
  unfold R.v49351, N.v49351.
  rewrite ?node_49346.
  rewrite ?node_49350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49352 (s : N.State) (i : N.Inputs) :
  R.v49352 (state s) (inputs i) = Zmod.unsigned (N.v49352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49352 s i)) at 1.
  unfold R.v49352, N.v49352.
  unfold R.v6, N.v6.
  rewrite ?node_49351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49353 (s : N.State) (i : N.Inputs) :
  R.v49353 (state s) (inputs i) = Zmod.unsigned (N.v49353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49353 s i)) at 1.
  unfold R.v49353, N.v49353.
  rewrite ?node_6589.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49354 (s : N.State) (i : N.Inputs) :
  R.v49354 (state s) (inputs i) = Zmod.unsigned (N.v49354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49354 s i)) at 1.
  unfold R.v49354, N.v49354.
  unfold R.v6, N.v6.
  rewrite ?node_6681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49355 (s : N.State) (i : N.Inputs) :
  R.v49355 (state s) (inputs i) = Zmod.unsigned (N.v49355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49355 s i)) at 1.
  unfold R.v49355, N.v49355.
  rewrite ?node_49353.
  rewrite ?node_49354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49356 (s : N.State) (i : N.Inputs) :
  R.v49356 (state s) (inputs i) = Zmod.unsigned (N.v49356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49356 s i)) at 1.
  unfold R.v49356, N.v49356.
  rewrite ?node_49352.
  rewrite ?node_49355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49357 (s : N.State) (i : N.Inputs) :
  R.v49357 (state s) (inputs i) = Zmod.unsigned (N.v49357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49357 s i)) at 1.
  unfold R.v49357, N.v49357.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49358 (s : N.State) (i : N.Inputs) :
  R.v49358 (state s) (inputs i) = Zmod.unsigned (N.v49358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49358 s i)) at 1.
  unfold R.v49358, N.v49358.
  rewrite ?node_6671.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49359 (s : N.State) (i : N.Inputs) :
  R.v49359 (state s) (inputs i) = Zmod.unsigned (N.v49359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49359 s i)) at 1.
  unfold R.v49359, N.v49359.
  rewrite ?node_6667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49360 (s : N.State) (i : N.Inputs) :
  R.v49360 (state s) (inputs i) = Zmod.unsigned (N.v49360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49360 s i)) at 1.
  unfold R.v49360, N.v49360.
  rewrite ?node_6663.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49361 (s : N.State) (i : N.Inputs) :
  R.v49361 (state s) (inputs i) = Zmod.unsigned (N.v49361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49361 s i)) at 1.
  unfold R.v49361, N.v49361.
  unfold R.v6, N.v6.
  rewrite ?node_6657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49362 (s : N.State) (i : N.Inputs) :
  R.v49362 (state s) (inputs i) = Zmod.unsigned (N.v49362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49362 s i)) at 1.
  unfold R.v49362, N.v49362.
  unfold R.v6, N.v6.
  rewrite ?node_6639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49363 (s : N.State) (i : N.Inputs) :
  R.v49363 (state s) (inputs i) = Zmod.unsigned (N.v49363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49363 s i)) at 1.
  unfold R.v49363, N.v49363.
  rewrite ?node_49361.
  rewrite ?node_49362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49364 (s : N.State) (i : N.Inputs) :
  R.v49364 (state s) (inputs i) = Zmod.unsigned (N.v49364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49364 s i)) at 1.
  unfold R.v49364, N.v49364.
  unfold R.v16484, N.v16484.
  rewrite ?node_49363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49365 (s : N.State) (i : N.Inputs) :
  R.v49365 (state s) (inputs i) = Zmod.unsigned (N.v49365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49365 s i)) at 1.
  unfold R.v49365, N.v49365.
  rewrite ?node_49358.
  rewrite ?node_49359.
  rewrite ?node_49360.
  rewrite ?node_49364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49366 (s : N.State) (i : N.Inputs) :
  R.v49366 (state s) (inputs i) = Zmod.unsigned (N.v49366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49366 s i)) at 1.
  unfold R.v49366, N.v49366.
  unfold R.v6, N.v6.
  rewrite ?node_49365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49367 (s : N.State) (i : N.Inputs) :
  R.v49367 (state s) (inputs i) = Zmod.unsigned (N.v49367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49367 s i)) at 1.
  unfold R.v49367, N.v49367.
  rewrite ?node_6672.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49368 (s : N.State) (i : N.Inputs) :
  R.v49368 (state s) (inputs i) = Zmod.unsigned (N.v49368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49368 s i)) at 1.
  unfold R.v49368, N.v49368.
  unfold R.v6, N.v6.
  rewrite ?node_6758.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49369 (s : N.State) (i : N.Inputs) :
  R.v49369 (state s) (inputs i) = Zmod.unsigned (N.v49369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49369 s i)) at 1.
  unfold R.v49369, N.v49369.
  unfold R.v6, N.v6.
  rewrite ?node_6768.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49370 (s : N.State) (i : N.Inputs) :
  R.v49370 (state s) (inputs i) = Zmod.unsigned (N.v49370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49370 s i)) at 1.
  unfold R.v49370, N.v49370.
  rewrite ?node_49367.
  rewrite ?node_49368.
  rewrite ?node_49369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49371 (s : N.State) (i : N.Inputs) :
  R.v49371 (state s) (inputs i) = Zmod.unsigned (N.v49371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49371 s i)) at 1.
  unfold R.v49371, N.v49371.
  rewrite ?node_49366.
  rewrite ?node_49370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49372 (s : N.State) (i : N.Inputs) :
  R.v49372 (state s) (inputs i) = Zmod.unsigned (N.v49372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49372 s i)) at 1.
  unfold R.v49372, N.v49372.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49373 (s : N.State) (i : N.Inputs) :
  R.v49373 (state s) (inputs i) = Zmod.unsigned (N.v49373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49373 s i)) at 1.
  unfold R.v49373, N.v49373.
  rewrite ?node_6663.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49374 (s : N.State) (i : N.Inputs) :
  R.v49374 (state s) (inputs i) = Zmod.unsigned (N.v49374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49374 s i)) at 1.
  unfold R.v49374, N.v49374.
  unfold R.v6, N.v6.
  rewrite ?node_6657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49375 (s : N.State) (i : N.Inputs) :
  R.v49375 (state s) (inputs i) = Zmod.unsigned (N.v49375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49375 s i)) at 1.
  unfold R.v49375, N.v49375.
  unfold R.v6, N.v6.
  rewrite ?node_6639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49376 (s : N.State) (i : N.Inputs) :
  R.v49376 (state s) (inputs i) = Zmod.unsigned (N.v49376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49376 s i)) at 1.
  unfold R.v49376, N.v49376.
  rewrite ?node_49374.
  rewrite ?node_49375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49377 (s : N.State) (i : N.Inputs) :
  R.v49377 (state s) (inputs i) = Zmod.unsigned (N.v49377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49377 s i)) at 1.
  unfold R.v49377, N.v49377.
  unfold R.v16484, N.v16484.
  rewrite ?node_49376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49378 (s : N.State) (i : N.Inputs) :
  R.v49378 (state s) (inputs i) = Zmod.unsigned (N.v49378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49378 s i)) at 1.
  unfold R.v49378, N.v49378.
  rewrite ?node_49373.
  rewrite ?node_49377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49379 (s : N.State) (i : N.Inputs) :
  R.v49379 (state s) (inputs i) = Zmod.unsigned (N.v49379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49379 s i)) at 1.
  unfold R.v49379, N.v49379.
  unfold R.v6, N.v6.
  rewrite ?node_49378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49380 (s : N.State) (i : N.Inputs) :
  R.v49380 (state s) (inputs i) = Zmod.unsigned (N.v49380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49380 s i)) at 1.
  unfold R.v49380, N.v49380.
  rewrite ?node_6664.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49381 (s : N.State) (i : N.Inputs) :
  R.v49381 (state s) (inputs i) = Zmod.unsigned (N.v49381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49381 s i)) at 1.
  unfold R.v49381, N.v49381.
  unfold R.v6, N.v6.
  rewrite ?node_6758.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49382 (s : N.State) (i : N.Inputs) :
  R.v49382 (state s) (inputs i) = Zmod.unsigned (N.v49382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49382 s i)) at 1.
  unfold R.v49382, N.v49382.
  rewrite ?node_49380.
  rewrite ?node_49381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49383 (s : N.State) (i : N.Inputs) :
  R.v49383 (state s) (inputs i) = Zmod.unsigned (N.v49383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49383 s i)) at 1.
  unfold R.v49383, N.v49383.
  rewrite ?node_49379.
  rewrite ?node_49382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49384 (s : N.State) (i : N.Inputs) :
  R.v49384 (state s) (inputs i) = Zmod.unsigned (N.v49384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49384 s i)) at 1.
  unfold R.v49384, N.v49384.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49385 (s : N.State) (i : N.Inputs) :
  R.v49385 (state s) (inputs i) = Zmod.unsigned (N.v49385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49385 s i)) at 1.
  unfold R.v49385, N.v49385.
  rewrite ?node_6671.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49386 (s : N.State) (i : N.Inputs) :
  R.v49386 (state s) (inputs i) = Zmod.unsigned (N.v49386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49386 s i)) at 1.
  unfold R.v49386, N.v49386.
  unfold R.v6, N.v6.
  rewrite ?node_6667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49387 (s : N.State) (i : N.Inputs) :
  R.v49387 (state s) (inputs i) = Zmod.unsigned (N.v49387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49387 s i)) at 1.
  unfold R.v49387, N.v49387.
  unfold R.v6, N.v6.
  rewrite ?node_6664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49388 (s : N.State) (i : N.Inputs) :
  R.v49388 (state s) (inputs i) = Zmod.unsigned (N.v49388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49388 s i)) at 1.
  unfold R.v49388, N.v49388.
  rewrite ?node_49386.
  rewrite ?node_49387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49389 (s : N.State) (i : N.Inputs) :
  R.v49389 (state s) (inputs i) = Zmod.unsigned (N.v49389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49389 s i)) at 1.
  unfold R.v49389, N.v49389.
  unfold R.v16484, N.v16484.
  rewrite ?node_49388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49390 (s : N.State) (i : N.Inputs) :
  R.v49390 (state s) (inputs i) = Zmod.unsigned (N.v49390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49390 s i)) at 1.
  unfold R.v49390, N.v49390.
  rewrite ?node_49385.
  rewrite ?node_49389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49391 (s : N.State) (i : N.Inputs) :
  R.v49391 (state s) (inputs i) = Zmod.unsigned (N.v49391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49391 s i)) at 1.
  unfold R.v49391, N.v49391.
  unfold R.v6, N.v6.
  rewrite ?node_49390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49392 (s : N.State) (i : N.Inputs) :
  R.v49392 (state s) (inputs i) = Zmod.unsigned (N.v49392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49392 s i)) at 1.
  unfold R.v49392, N.v49392.
  rewrite ?node_6672.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49393 (s : N.State) (i : N.Inputs) :
  R.v49393 (state s) (inputs i) = Zmod.unsigned (N.v49393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49393 s i)) at 1.
  unfold R.v49393, N.v49393.
  unfold R.v6, N.v6.
  rewrite ?node_6768.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49394 (s : N.State) (i : N.Inputs) :
  R.v49394 (state s) (inputs i) = Zmod.unsigned (N.v49394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49394 s i)) at 1.
  unfold R.v49394, N.v49394.
  rewrite ?node_49392.
  rewrite ?node_49393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49395 (s : N.State) (i : N.Inputs) :
  R.v49395 (state s) (inputs i) = Zmod.unsigned (N.v49395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49395 s i)) at 1.
  unfold R.v49395, N.v49395.
  rewrite ?node_49391.
  rewrite ?node_49394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49396 (s : N.State) (i : N.Inputs) :
  R.v49396 (state s) (inputs i) = Zmod.unsigned (N.v49396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49396 s i)) at 1.
  unfold R.v49396, N.v49396.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49397 (s : N.State) (i : N.Inputs) :
  R.v49397 (state s) (inputs i) = Zmod.unsigned (N.v49397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49397 s i)) at 1.
  unfold R.v49397, N.v49397.
  unfold R.v6, N.v6.
  rewrite ?node_6676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49398 (s : N.State) (i : N.Inputs) :
  R.v49398 (state s) (inputs i) = Zmod.unsigned (N.v49398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49398 s i)) at 1.
  unfold R.v49398, N.v49398.
  unfold R.v6, N.v6.
  rewrite ?node_6675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49399 (s : N.State) (i : N.Inputs) :
  R.v49399 (state s) (inputs i) = Zmod.unsigned (N.v49399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49399 s i)) at 1.
  unfold R.v49399, N.v49399.
  rewrite ?node_49397.
  rewrite ?node_49398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49400 (s : N.State) (i : N.Inputs) :
  R.v49400 (state s) (inputs i) = Zmod.unsigned (N.v49400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49400 s i)) at 1.
  unfold R.v49400, N.v49400.
  unfold R.v16463, N.v16463.
  rewrite ?node_49399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49401 (s : N.State) (i : N.Inputs) :
  R.v49401 (state s) (inputs i) = Zmod.unsigned (N.v49401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49401 s i)) at 1.
  unfold R.v49401, N.v49401.
  rewrite ?node_6677.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49402 (s : N.State) (i : N.Inputs) :
  R.v49402 (state s) (inputs i) = Zmod.unsigned (N.v49402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49402 s i)) at 1.
  unfold R.v49402, N.v49402.
  unfold R.v6, N.v6.
  rewrite ?node_6770.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49403 (s : N.State) (i : N.Inputs) :
  R.v49403 (state s) (inputs i) = Zmod.unsigned (N.v49403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49403 s i)) at 1.
  unfold R.v49403, N.v49403.
  rewrite ?node_49401.
  rewrite ?node_49402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49404 (s : N.State) (i : N.Inputs) :
  R.v49404 (state s) (inputs i) = Zmod.unsigned (N.v49404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49404 s i)) at 1.
  unfold R.v49404, N.v49404.
  rewrite ?node_49400.
  rewrite ?node_49403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49405 (s : N.State) (i : N.Inputs) :
  R.v49405 (state s) (inputs i) = Zmod.unsigned (N.v49405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49405 s i)) at 1.
  unfold R.v49405, N.v49405.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49406 (s : N.State) (i : N.Inputs) :
  R.v49406 (state s) (inputs i) = Zmod.unsigned (N.v49406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49406 s i)) at 1.
  unfold R.v49406, N.v49406.
  rewrite ?node_6758.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49407 (s : N.State) (i : N.Inputs) :
  R.v49407 (state s) (inputs i) = Zmod.unsigned (N.v49407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49407 s i)) at 1.
  unfold R.v49407, N.v49407.
  rewrite ?node_6754.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49408 (s : N.State) (i : N.Inputs) :
  R.v49408 (state s) (inputs i) = Zmod.unsigned (N.v49408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49408 s i)) at 1.
  unfold R.v49408, N.v49408.
  rewrite ?node_6750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49409 (s : N.State) (i : N.Inputs) :
  R.v49409 (state s) (inputs i) = Zmod.unsigned (N.v49409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49409 s i)) at 1.
  unfold R.v49409, N.v49409.
  unfold R.v6, N.v6.
  rewrite ?node_6742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49410 (s : N.State) (i : N.Inputs) :
  R.v49410 (state s) (inputs i) = Zmod.unsigned (N.v49410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49410 s i)) at 1.
  unfold R.v49410, N.v49410.
  unfold R.v6, N.v6.
  rewrite ?node_6724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49411 (s : N.State) (i : N.Inputs) :
  R.v49411 (state s) (inputs i) = Zmod.unsigned (N.v49411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49411 s i)) at 1.
  unfold R.v49411, N.v49411.
  rewrite ?node_49409.
  rewrite ?node_49410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49412 (s : N.State) (i : N.Inputs) :
  R.v49412 (state s) (inputs i) = Zmod.unsigned (N.v49412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49412 s i)) at 1.
  unfold R.v49412, N.v49412.
  unfold R.v16484, N.v16484.
  rewrite ?node_49411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49413 (s : N.State) (i : N.Inputs) :
  R.v49413 (state s) (inputs i) = Zmod.unsigned (N.v49413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49413 s i)) at 1.
  unfold R.v49413, N.v49413.
  rewrite ?node_49406.
  rewrite ?node_49407.
  rewrite ?node_49408.
  rewrite ?node_49412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49414 (s : N.State) (i : N.Inputs) :
  R.v49414 (state s) (inputs i) = Zmod.unsigned (N.v49414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49414 s i)) at 1.
  unfold R.v49414, N.v49414.
  unfold R.v6, N.v6.
  rewrite ?node_49413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49415 (s : N.State) (i : N.Inputs) :
  R.v49415 (state s) (inputs i) = Zmod.unsigned (N.v49415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49415 s i)) at 1.
  unfold R.v49415, N.v49415.
  rewrite ?node_6759.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49416 (s : N.State) (i : N.Inputs) :
  R.v49416 (state s) (inputs i) = Zmod.unsigned (N.v49416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49416 s i)) at 1.
  unfold R.v49416, N.v49416.
  unfold R.v6, N.v6.
  rewrite ?node_6848.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49417 (s : N.State) (i : N.Inputs) :
  R.v49417 (state s) (inputs i) = Zmod.unsigned (N.v49417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49417 s i)) at 1.
  unfold R.v49417, N.v49417.
  unfold R.v6, N.v6.
  rewrite ?node_6858.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49418 (s : N.State) (i : N.Inputs) :
  R.v49418 (state s) (inputs i) = Zmod.unsigned (N.v49418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49418 s i)) at 1.
  unfold R.v49418, N.v49418.
  rewrite ?node_49415.
  rewrite ?node_49416.
  rewrite ?node_49417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49419 (s : N.State) (i : N.Inputs) :
  R.v49419 (state s) (inputs i) = Zmod.unsigned (N.v49419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49419 s i)) at 1.
  unfold R.v49419, N.v49419.
  rewrite ?node_49414.
  rewrite ?node_49418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49420 (s : N.State) (i : N.Inputs) :
  R.v49420 (state s) (inputs i) = Zmod.unsigned (N.v49420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49420 s i)) at 1.
  unfold R.v49420, N.v49420.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49421 (s : N.State) (i : N.Inputs) :
  R.v49421 (state s) (inputs i) = Zmod.unsigned (N.v49421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49421 s i)) at 1.
  unfold R.v49421, N.v49421.
  rewrite ?node_6750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49422 (s : N.State) (i : N.Inputs) :
  R.v49422 (state s) (inputs i) = Zmod.unsigned (N.v49422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49422 s i)) at 1.
  unfold R.v49422, N.v49422.
  unfold R.v6, N.v6.
  rewrite ?node_6742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49423 (s : N.State) (i : N.Inputs) :
  R.v49423 (state s) (inputs i) = Zmod.unsigned (N.v49423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49423 s i)) at 1.
  unfold R.v49423, N.v49423.
  unfold R.v6, N.v6.
  rewrite ?node_6724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49424 (s : N.State) (i : N.Inputs) :
  R.v49424 (state s) (inputs i) = Zmod.unsigned (N.v49424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49424 s i)) at 1.
  unfold R.v49424, N.v49424.
  rewrite ?node_49422.
  rewrite ?node_49423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49425 (s : N.State) (i : N.Inputs) :
  R.v49425 (state s) (inputs i) = Zmod.unsigned (N.v49425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49425 s i)) at 1.
  unfold R.v49425, N.v49425.
  unfold R.v16484, N.v16484.
  rewrite ?node_49424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49426 (s : N.State) (i : N.Inputs) :
  R.v49426 (state s) (inputs i) = Zmod.unsigned (N.v49426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49426 s i)) at 1.
  unfold R.v49426, N.v49426.
  rewrite ?node_49421.
  rewrite ?node_49425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49427 (s : N.State) (i : N.Inputs) :
  R.v49427 (state s) (inputs i) = Zmod.unsigned (N.v49427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49427 s i)) at 1.
  unfold R.v49427, N.v49427.
  unfold R.v6, N.v6.
  rewrite ?node_49426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49428 (s : N.State) (i : N.Inputs) :
  R.v49428 (state s) (inputs i) = Zmod.unsigned (N.v49428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49428 s i)) at 1.
  unfold R.v49428, N.v49428.
  rewrite ?node_6751.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49429 (s : N.State) (i : N.Inputs) :
  R.v49429 (state s) (inputs i) = Zmod.unsigned (N.v49429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49429 s i)) at 1.
  unfold R.v49429, N.v49429.
  unfold R.v6, N.v6.
  rewrite ?node_6848.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49430 (s : N.State) (i : N.Inputs) :
  R.v49430 (state s) (inputs i) = Zmod.unsigned (N.v49430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49430 s i)) at 1.
  unfold R.v49430, N.v49430.
  rewrite ?node_49428.
  rewrite ?node_49429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49431 (s : N.State) (i : N.Inputs) :
  R.v49431 (state s) (inputs i) = Zmod.unsigned (N.v49431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49431 s i)) at 1.
  unfold R.v49431, N.v49431.
  rewrite ?node_49427.
  rewrite ?node_49430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49432 (s : N.State) (i : N.Inputs) :
  R.v49432 (state s) (inputs i) = Zmod.unsigned (N.v49432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49432 s i)) at 1.
  unfold R.v49432, N.v49432.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49433 (s : N.State) (i : N.Inputs) :
  R.v49433 (state s) (inputs i) = Zmod.unsigned (N.v49433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49433 s i)) at 1.
  unfold R.v49433, N.v49433.
  rewrite ?node_6758.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49434 (s : N.State) (i : N.Inputs) :
  R.v49434 (state s) (inputs i) = Zmod.unsigned (N.v49434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49434 s i)) at 1.
  unfold R.v49434, N.v49434.
  unfold R.v6, N.v6.
  rewrite ?node_6754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49435 (s : N.State) (i : N.Inputs) :
  R.v49435 (state s) (inputs i) = Zmod.unsigned (N.v49435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49435 s i)) at 1.
  unfold R.v49435, N.v49435.
  unfold R.v6, N.v6.
  rewrite ?node_6751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49436 (s : N.State) (i : N.Inputs) :
  R.v49436 (state s) (inputs i) = Zmod.unsigned (N.v49436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49436 s i)) at 1.
  unfold R.v49436, N.v49436.
  rewrite ?node_49434.
  rewrite ?node_49435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49437 (s : N.State) (i : N.Inputs) :
  R.v49437 (state s) (inputs i) = Zmod.unsigned (N.v49437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49437 s i)) at 1.
  unfold R.v49437, N.v49437.
  unfold R.v16484, N.v16484.
  rewrite ?node_49436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49438 (s : N.State) (i : N.Inputs) :
  R.v49438 (state s) (inputs i) = Zmod.unsigned (N.v49438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49438 s i)) at 1.
  unfold R.v49438, N.v49438.
  rewrite ?node_49433.
  rewrite ?node_49437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49439 (s : N.State) (i : N.Inputs) :
  R.v49439 (state s) (inputs i) = Zmod.unsigned (N.v49439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49439 s i)) at 1.
  unfold R.v49439, N.v49439.
  unfold R.v6, N.v6.
  rewrite ?node_49438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49440 (s : N.State) (i : N.Inputs) :
  R.v49440 (state s) (inputs i) = Zmod.unsigned (N.v49440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49440 s i)) at 1.
  unfold R.v49440, N.v49440.
  rewrite ?node_6759.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49441 (s : N.State) (i : N.Inputs) :
  R.v49441 (state s) (inputs i) = Zmod.unsigned (N.v49441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49441 s i)) at 1.
  unfold R.v49441, N.v49441.
  unfold R.v6, N.v6.
  rewrite ?node_6858.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49442 (s : N.State) (i : N.Inputs) :
  R.v49442 (state s) (inputs i) = Zmod.unsigned (N.v49442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49442 s i)) at 1.
  unfold R.v49442, N.v49442.
  rewrite ?node_49440.
  rewrite ?node_49441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49443 (s : N.State) (i : N.Inputs) :
  R.v49443 (state s) (inputs i) = Zmod.unsigned (N.v49443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49443 s i)) at 1.
  unfold R.v49443, N.v49443.
  rewrite ?node_49439.
  rewrite ?node_49442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49444 (s : N.State) (i : N.Inputs) :
  R.v49444 (state s) (inputs i) = Zmod.unsigned (N.v49444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49444 s i)) at 1.
  unfold R.v49444, N.v49444.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49445 (s : N.State) (i : N.Inputs) :
  R.v49445 (state s) (inputs i) = Zmod.unsigned (N.v49445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49445 s i)) at 1.
  unfold R.v49445, N.v49445.
  unfold R.v6, N.v6.
  rewrite ?node_6763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49446 (s : N.State) (i : N.Inputs) :
  R.v49446 (state s) (inputs i) = Zmod.unsigned (N.v49446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49446 s i)) at 1.
  unfold R.v49446, N.v49446.
  unfold R.v6, N.v6.
  rewrite ?node_6762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49447 (s : N.State) (i : N.Inputs) :
  R.v49447 (state s) (inputs i) = Zmod.unsigned (N.v49447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49447 s i)) at 1.
  unfold R.v49447, N.v49447.
  rewrite ?node_49445.
  rewrite ?node_49446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49448 (s : N.State) (i : N.Inputs) :
  R.v49448 (state s) (inputs i) = Zmod.unsigned (N.v49448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49448 s i)) at 1.
  unfold R.v49448, N.v49448.
  unfold R.v16463, N.v16463.
  rewrite ?node_49447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49449 (s : N.State) (i : N.Inputs) :
  R.v49449 (state s) (inputs i) = Zmod.unsigned (N.v49449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49449 s i)) at 1.
  unfold R.v49449, N.v49449.
  rewrite ?node_6764.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49450 (s : N.State) (i : N.Inputs) :
  R.v49450 (state s) (inputs i) = Zmod.unsigned (N.v49450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49450 s i)) at 1.
  unfold R.v49450, N.v49450.
  unfold R.v6, N.v6.
  rewrite ?node_6860.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49451 (s : N.State) (i : N.Inputs) :
  R.v49451 (state s) (inputs i) = Zmod.unsigned (N.v49451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49451 s i)) at 1.
  unfold R.v49451, N.v49451.
  rewrite ?node_49449.
  rewrite ?node_49450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49452 (s : N.State) (i : N.Inputs) :
  R.v49452 (state s) (inputs i) = Zmod.unsigned (N.v49452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49452 s i)) at 1.
  unfold R.v49452, N.v49452.
  rewrite ?node_49448.
  rewrite ?node_49451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49453 (s : N.State) (i : N.Inputs) :
  R.v49453 (state s) (inputs i) = Zmod.unsigned (N.v49453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49453 s i)) at 1.
  unfold R.v49453, N.v49453.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49454 (s : N.State) (i : N.Inputs) :
  R.v49454 (state s) (inputs i) = Zmod.unsigned (N.v49454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49454 s i)) at 1.
  unfold R.v49454, N.v49454.
  rewrite ?node_6848.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49455 (s : N.State) (i : N.Inputs) :
  R.v49455 (state s) (inputs i) = Zmod.unsigned (N.v49455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49455 s i)) at 1.
  unfold R.v49455, N.v49455.
  rewrite ?node_6844.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49456 (s : N.State) (i : N.Inputs) :
  R.v49456 (state s) (inputs i) = Zmod.unsigned (N.v49456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49456 s i)) at 1.
  unfold R.v49456, N.v49456.
  rewrite ?node_6840.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49457 (s : N.State) (i : N.Inputs) :
  R.v49457 (state s) (inputs i) = Zmod.unsigned (N.v49457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49457 s i)) at 1.
  unfold R.v49457, N.v49457.
  unfold R.v6, N.v6.
  rewrite ?node_6832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49458 (s : N.State) (i : N.Inputs) :
  R.v49458 (state s) (inputs i) = Zmod.unsigned (N.v49458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49458 s i)) at 1.
  unfold R.v49458, N.v49458.
  unfold R.v6, N.v6.
  rewrite ?node_6813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49459 (s : N.State) (i : N.Inputs) :
  R.v49459 (state s) (inputs i) = Zmod.unsigned (N.v49459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49459 s i)) at 1.
  unfold R.v49459, N.v49459.
  rewrite ?node_49457.
  rewrite ?node_49458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49460 (s : N.State) (i : N.Inputs) :
  R.v49460 (state s) (inputs i) = Zmod.unsigned (N.v49460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49460 s i)) at 1.
  unfold R.v49460, N.v49460.
  unfold R.v16484, N.v16484.
  rewrite ?node_49459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49461 (s : N.State) (i : N.Inputs) :
  R.v49461 (state s) (inputs i) = Zmod.unsigned (N.v49461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49461 s i)) at 1.
  unfold R.v49461, N.v49461.
  rewrite ?node_49454.
  rewrite ?node_49455.
  rewrite ?node_49456.
  rewrite ?node_49460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49462 (s : N.State) (i : N.Inputs) :
  R.v49462 (state s) (inputs i) = Zmod.unsigned (N.v49462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49462 s i)) at 1.
  unfold R.v49462, N.v49462.
  unfold R.v6, N.v6.
  rewrite ?node_49461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49463 (s : N.State) (i : N.Inputs) :
  R.v49463 (state s) (inputs i) = Zmod.unsigned (N.v49463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49463 s i)) at 1.
  unfold R.v49463, N.v49463.
  rewrite ?node_6849.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49464 (s : N.State) (i : N.Inputs) :
  R.v49464 (state s) (inputs i) = Zmod.unsigned (N.v49464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49464 s i)) at 1.
  unfold R.v49464, N.v49464.
  unfold R.v6, N.v6.
  rewrite ?node_6942.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49465 (s : N.State) (i : N.Inputs) :
  R.v49465 (state s) (inputs i) = Zmod.unsigned (N.v49465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49465 s i)) at 1.
  unfold R.v49465, N.v49465.
  unfold R.v6, N.v6.
  rewrite ?node_6952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49466 (s : N.State) (i : N.Inputs) :
  R.v49466 (state s) (inputs i) = Zmod.unsigned (N.v49466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49466 s i)) at 1.
  unfold R.v49466, N.v49466.
  rewrite ?node_49463.
  rewrite ?node_49464.
  rewrite ?node_49465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49467 (s : N.State) (i : N.Inputs) :
  R.v49467 (state s) (inputs i) = Zmod.unsigned (N.v49467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49467 s i)) at 1.
  unfold R.v49467, N.v49467.
  rewrite ?node_49462.
  rewrite ?node_49466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49468 (s : N.State) (i : N.Inputs) :
  R.v49468 (state s) (inputs i) = Zmod.unsigned (N.v49468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49468 s i)) at 1.
  unfold R.v49468, N.v49468.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49469 (s : N.State) (i : N.Inputs) :
  R.v49469 (state s) (inputs i) = Zmod.unsigned (N.v49469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49469 s i)) at 1.
  unfold R.v49469, N.v49469.
  rewrite ?node_6840.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49470 (s : N.State) (i : N.Inputs) :
  R.v49470 (state s) (inputs i) = Zmod.unsigned (N.v49470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49470 s i)) at 1.
  unfold R.v49470, N.v49470.
  unfold R.v6, N.v6.
  rewrite ?node_6832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49471 (s : N.State) (i : N.Inputs) :
  R.v49471 (state s) (inputs i) = Zmod.unsigned (N.v49471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49471 s i)) at 1.
  unfold R.v49471, N.v49471.
  unfold R.v6, N.v6.
  rewrite ?node_6813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49472 (s : N.State) (i : N.Inputs) :
  R.v49472 (state s) (inputs i) = Zmod.unsigned (N.v49472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49472 s i)) at 1.
  unfold R.v49472, N.v49472.
  rewrite ?node_49470.
  rewrite ?node_49471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49473 (s : N.State) (i : N.Inputs) :
  R.v49473 (state s) (inputs i) = Zmod.unsigned (N.v49473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49473 s i)) at 1.
  unfold R.v49473, N.v49473.
  unfold R.v16484, N.v16484.
  rewrite ?node_49472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49474 (s : N.State) (i : N.Inputs) :
  R.v49474 (state s) (inputs i) = Zmod.unsigned (N.v49474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49474 s i)) at 1.
  unfold R.v49474, N.v49474.
  rewrite ?node_49469.
  rewrite ?node_49473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49475 (s : N.State) (i : N.Inputs) :
  R.v49475 (state s) (inputs i) = Zmod.unsigned (N.v49475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49475 s i)) at 1.
  unfold R.v49475, N.v49475.
  unfold R.v6, N.v6.
  rewrite ?node_49474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49476 (s : N.State) (i : N.Inputs) :
  R.v49476 (state s) (inputs i) = Zmod.unsigned (N.v49476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49476 s i)) at 1.
  unfold R.v49476, N.v49476.
  rewrite ?node_6841.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49477 (s : N.State) (i : N.Inputs) :
  R.v49477 (state s) (inputs i) = Zmod.unsigned (N.v49477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49477 s i)) at 1.
  unfold R.v49477, N.v49477.
  unfold R.v6, N.v6.
  rewrite ?node_6942.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49478 (s : N.State) (i : N.Inputs) :
  R.v49478 (state s) (inputs i) = Zmod.unsigned (N.v49478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49478 s i)) at 1.
  unfold R.v49478, N.v49478.
  rewrite ?node_49476.
  rewrite ?node_49477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49479 (s : N.State) (i : N.Inputs) :
  R.v49479 (state s) (inputs i) = Zmod.unsigned (N.v49479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49479 s i)) at 1.
  unfold R.v49479, N.v49479.
  rewrite ?node_49475.
  rewrite ?node_49478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49480 (s : N.State) (i : N.Inputs) :
  R.v49480 (state s) (inputs i) = Zmod.unsigned (N.v49480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49480 s i)) at 1.
  unfold R.v49480, N.v49480.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49481 (s : N.State) (i : N.Inputs) :
  R.v49481 (state s) (inputs i) = Zmod.unsigned (N.v49481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49481 s i)) at 1.
  unfold R.v49481, N.v49481.
  rewrite ?node_6848.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49482 (s : N.State) (i : N.Inputs) :
  R.v49482 (state s) (inputs i) = Zmod.unsigned (N.v49482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49482 s i)) at 1.
  unfold R.v49482, N.v49482.
  unfold R.v6, N.v6.
  rewrite ?node_6844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49483 (s : N.State) (i : N.Inputs) :
  R.v49483 (state s) (inputs i) = Zmod.unsigned (N.v49483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49483 s i)) at 1.
  unfold R.v49483, N.v49483.
  unfold R.v6, N.v6.
  rewrite ?node_6841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49484 (s : N.State) (i : N.Inputs) :
  R.v49484 (state s) (inputs i) = Zmod.unsigned (N.v49484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49484 s i)) at 1.
  unfold R.v49484, N.v49484.
  rewrite ?node_49482.
  rewrite ?node_49483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49485 (s : N.State) (i : N.Inputs) :
  R.v49485 (state s) (inputs i) = Zmod.unsigned (N.v49485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49485 s i)) at 1.
  unfold R.v49485, N.v49485.
  unfold R.v16484, N.v16484.
  rewrite ?node_49484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49486 (s : N.State) (i : N.Inputs) :
  R.v49486 (state s) (inputs i) = Zmod.unsigned (N.v49486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49486 s i)) at 1.
  unfold R.v49486, N.v49486.
  rewrite ?node_49481.
  rewrite ?node_49485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49487 (s : N.State) (i : N.Inputs) :
  R.v49487 (state s) (inputs i) = Zmod.unsigned (N.v49487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49487 s i)) at 1.
  unfold R.v49487, N.v49487.
  unfold R.v6, N.v6.
  rewrite ?node_49486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49488 (s : N.State) (i : N.Inputs) :
  R.v49488 (state s) (inputs i) = Zmod.unsigned (N.v49488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49488 s i)) at 1.
  unfold R.v49488, N.v49488.
  rewrite ?node_6849.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49489 (s : N.State) (i : N.Inputs) :
  R.v49489 (state s) (inputs i) = Zmod.unsigned (N.v49489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49489 s i)) at 1.
  unfold R.v49489, N.v49489.
  unfold R.v6, N.v6.
  rewrite ?node_6952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49490 (s : N.State) (i : N.Inputs) :
  R.v49490 (state s) (inputs i) = Zmod.unsigned (N.v49490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49490 s i)) at 1.
  unfold R.v49490, N.v49490.
  rewrite ?node_49488.
  rewrite ?node_49489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49491 (s : N.State) (i : N.Inputs) :
  R.v49491 (state s) (inputs i) = Zmod.unsigned (N.v49491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49491 s i)) at 1.
  unfold R.v49491, N.v49491.
  rewrite ?node_49487.
  rewrite ?node_49490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49492 (s : N.State) (i : N.Inputs) :
  R.v49492 (state s) (inputs i) = Zmod.unsigned (N.v49492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49492 s i)) at 1.
  unfold R.v49492, N.v49492.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49493 (s : N.State) (i : N.Inputs) :
  R.v49493 (state s) (inputs i) = Zmod.unsigned (N.v49493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49493 s i)) at 1.
  unfold R.v49493, N.v49493.
  unfold R.v6, N.v6.
  rewrite ?node_6853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49494 (s : N.State) (i : N.Inputs) :
  R.v49494 (state s) (inputs i) = Zmod.unsigned (N.v49494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49494 s i)) at 1.
  unfold R.v49494, N.v49494.
  unfold R.v6, N.v6.
  rewrite ?node_6852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49495 (s : N.State) (i : N.Inputs) :
  R.v49495 (state s) (inputs i) = Zmod.unsigned (N.v49495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49495 s i)) at 1.
  unfold R.v49495, N.v49495.
  rewrite ?node_49493.
  rewrite ?node_49494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49496 (s : N.State) (i : N.Inputs) :
  R.v49496 (state s) (inputs i) = Zmod.unsigned (N.v49496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49496 s i)) at 1.
  unfold R.v49496, N.v49496.
  unfold R.v16463, N.v16463.
  rewrite ?node_49495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49497 (s : N.State) (i : N.Inputs) :
  R.v49497 (state s) (inputs i) = Zmod.unsigned (N.v49497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49497 s i)) at 1.
  unfold R.v49497, N.v49497.
  rewrite ?node_6854.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49498 (s : N.State) (i : N.Inputs) :
  R.v49498 (state s) (inputs i) = Zmod.unsigned (N.v49498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49498 s i)) at 1.
  unfold R.v49498, N.v49498.
  unfold R.v6, N.v6.
  rewrite ?node_6954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49499 (s : N.State) (i : N.Inputs) :
  R.v49499 (state s) (inputs i) = Zmod.unsigned (N.v49499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49499 s i)) at 1.
  unfold R.v49499, N.v49499.
  rewrite ?node_49497.
  rewrite ?node_49498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49500 (s : N.State) (i : N.Inputs) :
  R.v49500 (state s) (inputs i) = Zmod.unsigned (N.v49500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49500 s i)) at 1.
  unfold R.v49500, N.v49500.
  rewrite ?node_49496.
  rewrite ?node_49499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49501 (s : N.State) (i : N.Inputs) :
  R.v49501 (state s) (inputs i) = Zmod.unsigned (N.v49501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49501 s i)) at 1.
  unfold R.v49501, N.v49501.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49502 (s : N.State) (i : N.Inputs) :
  R.v49502 (state s) (inputs i) = Zmod.unsigned (N.v49502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49502 s i)) at 1.
  unfold R.v49502, N.v49502.
  rewrite ?node_6942.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49503 (s : N.State) (i : N.Inputs) :
  R.v49503 (state s) (inputs i) = Zmod.unsigned (N.v49503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49503 s i)) at 1.
  unfold R.v49503, N.v49503.
  rewrite ?node_6938.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49504 (s : N.State) (i : N.Inputs) :
  R.v49504 (state s) (inputs i) = Zmod.unsigned (N.v49504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49504 s i)) at 1.
  unfold R.v49504, N.v49504.
  rewrite ?node_6934.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49505 (s : N.State) (i : N.Inputs) :
  R.v49505 (state s) (inputs i) = Zmod.unsigned (N.v49505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49505 s i)) at 1.
  unfold R.v49505, N.v49505.
  unfold R.v6, N.v6.
  rewrite ?node_6928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49506 (s : N.State) (i : N.Inputs) :
  R.v49506 (state s) (inputs i) = Zmod.unsigned (N.v49506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49506 s i)) at 1.
  unfold R.v49506, N.v49506.
  unfold R.v6, N.v6.
  rewrite ?node_6905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49507 (s : N.State) (i : N.Inputs) :
  R.v49507 (state s) (inputs i) = Zmod.unsigned (N.v49507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49507 s i)) at 1.
  unfold R.v49507, N.v49507.
  rewrite ?node_49505.
  rewrite ?node_49506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49508 (s : N.State) (i : N.Inputs) :
  R.v49508 (state s) (inputs i) = Zmod.unsigned (N.v49508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49508 s i)) at 1.
  unfold R.v49508, N.v49508.
  unfold R.v16484, N.v16484.
  rewrite ?node_49507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49509 (s : N.State) (i : N.Inputs) :
  R.v49509 (state s) (inputs i) = Zmod.unsigned (N.v49509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49509 s i)) at 1.
  unfold R.v49509, N.v49509.
  rewrite ?node_49502.
  rewrite ?node_49503.
  rewrite ?node_49504.
  rewrite ?node_49508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49510 (s : N.State) (i : N.Inputs) :
  R.v49510 (state s) (inputs i) = Zmod.unsigned (N.v49510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49510 s i)) at 1.
  unfold R.v49510, N.v49510.
  unfold R.v6, N.v6.
  rewrite ?node_49509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49511 (s : N.State) (i : N.Inputs) :
  R.v49511 (state s) (inputs i) = Zmod.unsigned (N.v49511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49511 s i)) at 1.
  unfold R.v49511, N.v49511.
  rewrite ?node_6943.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49512 (s : N.State) (i : N.Inputs) :
  R.v49512 (state s) (inputs i) = Zmod.unsigned (N.v49512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49512 s i)) at 1.
  unfold R.v49512, N.v49512.
  unfold R.v6, N.v6.
  rewrite ?node_7041.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49513 (s : N.State) (i : N.Inputs) :
  R.v49513 (state s) (inputs i) = Zmod.unsigned (N.v49513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49513 s i)) at 1.
  unfold R.v49513, N.v49513.
  unfold R.v6, N.v6.
  rewrite ?node_7051.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49514 (s : N.State) (i : N.Inputs) :
  R.v49514 (state s) (inputs i) = Zmod.unsigned (N.v49514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49514 s i)) at 1.
  unfold R.v49514, N.v49514.
  rewrite ?node_49511.
  rewrite ?node_49512.
  rewrite ?node_49513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49515 (s : N.State) (i : N.Inputs) :
  R.v49515 (state s) (inputs i) = Zmod.unsigned (N.v49515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49515 s i)) at 1.
  unfold R.v49515, N.v49515.
  rewrite ?node_49510.
  rewrite ?node_49514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49516 (s : N.State) (i : N.Inputs) :
  R.v49516 (state s) (inputs i) = Zmod.unsigned (N.v49516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49516 s i)) at 1.
  unfold R.v49516, N.v49516.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49517 (s : N.State) (i : N.Inputs) :
  R.v49517 (state s) (inputs i) = Zmod.unsigned (N.v49517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49517 s i)) at 1.
  unfold R.v49517, N.v49517.
  rewrite ?node_6934.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49518 (s : N.State) (i : N.Inputs) :
  R.v49518 (state s) (inputs i) = Zmod.unsigned (N.v49518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49518 s i)) at 1.
  unfold R.v49518, N.v49518.
  unfold R.v6, N.v6.
  rewrite ?node_6928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49519 (s : N.State) (i : N.Inputs) :
  R.v49519 (state s) (inputs i) = Zmod.unsigned (N.v49519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49519 s i)) at 1.
  unfold R.v49519, N.v49519.
  unfold R.v6, N.v6.
  rewrite ?node_6905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49520 (s : N.State) (i : N.Inputs) :
  R.v49520 (state s) (inputs i) = Zmod.unsigned (N.v49520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49520 s i)) at 1.
  unfold R.v49520, N.v49520.
  rewrite ?node_49518.
  rewrite ?node_49519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49521 (s : N.State) (i : N.Inputs) :
  R.v49521 (state s) (inputs i) = Zmod.unsigned (N.v49521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49521 s i)) at 1.
  unfold R.v49521, N.v49521.
  unfold R.v16484, N.v16484.
  rewrite ?node_49520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49522 (s : N.State) (i : N.Inputs) :
  R.v49522 (state s) (inputs i) = Zmod.unsigned (N.v49522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49522 s i)) at 1.
  unfold R.v49522, N.v49522.
  rewrite ?node_49517.
  rewrite ?node_49521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49523 (s : N.State) (i : N.Inputs) :
  R.v49523 (state s) (inputs i) = Zmod.unsigned (N.v49523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49523 s i)) at 1.
  unfold R.v49523, N.v49523.
  unfold R.v6, N.v6.
  rewrite ?node_49522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49524 (s : N.State) (i : N.Inputs) :
  R.v49524 (state s) (inputs i) = Zmod.unsigned (N.v49524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49524 s i)) at 1.
  unfold R.v49524, N.v49524.
  rewrite ?node_6935.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49525 (s : N.State) (i : N.Inputs) :
  R.v49525 (state s) (inputs i) = Zmod.unsigned (N.v49525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49525 s i)) at 1.
  unfold R.v49525, N.v49525.
  unfold R.v6, N.v6.
  rewrite ?node_7041.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49526 (s : N.State) (i : N.Inputs) :
  R.v49526 (state s) (inputs i) = Zmod.unsigned (N.v49526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49526 s i)) at 1.
  unfold R.v49526, N.v49526.
  rewrite ?node_49524.
  rewrite ?node_49525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49527 (s : N.State) (i : N.Inputs) :
  R.v49527 (state s) (inputs i) = Zmod.unsigned (N.v49527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49527 s i)) at 1.
  unfold R.v49527, N.v49527.
  rewrite ?node_49523.
  rewrite ?node_49526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49528 (s : N.State) (i : N.Inputs) :
  R.v49528 (state s) (inputs i) = Zmod.unsigned (N.v49528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49528 s i)) at 1.
  unfold R.v49528, N.v49528.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49529 (s : N.State) (i : N.Inputs) :
  R.v49529 (state s) (inputs i) = Zmod.unsigned (N.v49529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49529 s i)) at 1.
  unfold R.v49529, N.v49529.
  rewrite ?node_6942.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49530 (s : N.State) (i : N.Inputs) :
  R.v49530 (state s) (inputs i) = Zmod.unsigned (N.v49530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49530 s i)) at 1.
  unfold R.v49530, N.v49530.
  unfold R.v6, N.v6.
  rewrite ?node_6938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49531 (s : N.State) (i : N.Inputs) :
  R.v49531 (state s) (inputs i) = Zmod.unsigned (N.v49531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49531 s i)) at 1.
  unfold R.v49531, N.v49531.
  unfold R.v6, N.v6.
  rewrite ?node_6935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49532 (s : N.State) (i : N.Inputs) :
  R.v49532 (state s) (inputs i) = Zmod.unsigned (N.v49532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49532 s i)) at 1.
  unfold R.v49532, N.v49532.
  rewrite ?node_49530.
  rewrite ?node_49531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49533 (s : N.State) (i : N.Inputs) :
  R.v49533 (state s) (inputs i) = Zmod.unsigned (N.v49533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49533 s i)) at 1.
  unfold R.v49533, N.v49533.
  unfold R.v16484, N.v16484.
  rewrite ?node_49532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49534 (s : N.State) (i : N.Inputs) :
  R.v49534 (state s) (inputs i) = Zmod.unsigned (N.v49534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49534 s i)) at 1.
  unfold R.v49534, N.v49534.
  rewrite ?node_49529.
  rewrite ?node_49533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49535 (s : N.State) (i : N.Inputs) :
  R.v49535 (state s) (inputs i) = Zmod.unsigned (N.v49535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49535 s i)) at 1.
  unfold R.v49535, N.v49535.
  unfold R.v6, N.v6.
  rewrite ?node_49534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49536 (s : N.State) (i : N.Inputs) :
  R.v49536 (state s) (inputs i) = Zmod.unsigned (N.v49536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49536 s i)) at 1.
  unfold R.v49536, N.v49536.
  rewrite ?node_6943.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49537 (s : N.State) (i : N.Inputs) :
  R.v49537 (state s) (inputs i) = Zmod.unsigned (N.v49537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49537 s i)) at 1.
  unfold R.v49537, N.v49537.
  unfold R.v6, N.v6.
  rewrite ?node_7051.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49538 (s : N.State) (i : N.Inputs) :
  R.v49538 (state s) (inputs i) = Zmod.unsigned (N.v49538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49538 s i)) at 1.
  unfold R.v49538, N.v49538.
  rewrite ?node_49536.
  rewrite ?node_49537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49539 (s : N.State) (i : N.Inputs) :
  R.v49539 (state s) (inputs i) = Zmod.unsigned (N.v49539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49539 s i)) at 1.
  unfold R.v49539, N.v49539.
  rewrite ?node_49535.
  rewrite ?node_49538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49540 (s : N.State) (i : N.Inputs) :
  R.v49540 (state s) (inputs i) = Zmod.unsigned (N.v49540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49540 s i)) at 1.
  unfold R.v49540, N.v49540.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49541 (s : N.State) (i : N.Inputs) :
  R.v49541 (state s) (inputs i) = Zmod.unsigned (N.v49541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49541 s i)) at 1.
  unfold R.v49541, N.v49541.
  unfold R.v6, N.v6.
  rewrite ?node_6947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49542 (s : N.State) (i : N.Inputs) :
  R.v49542 (state s) (inputs i) = Zmod.unsigned (N.v49542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49542 s i)) at 1.
  unfold R.v49542, N.v49542.
  unfold R.v6, N.v6.
  rewrite ?node_6946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49543 (s : N.State) (i : N.Inputs) :
  R.v49543 (state s) (inputs i) = Zmod.unsigned (N.v49543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49543 s i)) at 1.
  unfold R.v49543, N.v49543.
  rewrite ?node_49541.
  rewrite ?node_49542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49544 (s : N.State) (i : N.Inputs) :
  R.v49544 (state s) (inputs i) = Zmod.unsigned (N.v49544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49544 s i)) at 1.
  unfold R.v49544, N.v49544.
  unfold R.v16463, N.v16463.
  rewrite ?node_49543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49545 (s : N.State) (i : N.Inputs) :
  R.v49545 (state s) (inputs i) = Zmod.unsigned (N.v49545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49545 s i)) at 1.
  unfold R.v49545, N.v49545.
  rewrite ?node_6948.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49546 (s : N.State) (i : N.Inputs) :
  R.v49546 (state s) (inputs i) = Zmod.unsigned (N.v49546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49546 s i)) at 1.
  unfold R.v49546, N.v49546.
  unfold R.v6, N.v6.
  rewrite ?node_7053.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49547 (s : N.State) (i : N.Inputs) :
  R.v49547 (state s) (inputs i) = Zmod.unsigned (N.v49547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49547 s i)) at 1.
  unfold R.v49547, N.v49547.
  rewrite ?node_49545.
  rewrite ?node_49546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49548 (s : N.State) (i : N.Inputs) :
  R.v49548 (state s) (inputs i) = Zmod.unsigned (N.v49548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49548 s i)) at 1.
  unfold R.v49548, N.v49548.
  rewrite ?node_49544.
  rewrite ?node_49547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49549 (s : N.State) (i : N.Inputs) :
  R.v49549 (state s) (inputs i) = Zmod.unsigned (N.v49549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49549 s i)) at 1.
  unfold R.v49549, N.v49549.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49550 (s : N.State) (i : N.Inputs) :
  R.v49550 (state s) (inputs i) = Zmod.unsigned (N.v49550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49550 s i)) at 1.
  unfold R.v49550, N.v49550.
  rewrite ?node_7041.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49551 (s : N.State) (i : N.Inputs) :
  R.v49551 (state s) (inputs i) = Zmod.unsigned (N.v49551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49551 s i)) at 1.
  unfold R.v49551, N.v49551.
  rewrite ?node_7037.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49552 (s : N.State) (i : N.Inputs) :
  R.v49552 (state s) (inputs i) = Zmod.unsigned (N.v49552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49552 s i)) at 1.
  unfold R.v49552, N.v49552.
  rewrite ?node_7033.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49553 (s : N.State) (i : N.Inputs) :
  R.v49553 (state s) (inputs i) = Zmod.unsigned (N.v49553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49553 s i)) at 1.
  unfold R.v49553, N.v49553.
  unfold R.v6, N.v6.
  rewrite ?node_7021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49554 (s : N.State) (i : N.Inputs) :
  R.v49554 (state s) (inputs i) = Zmod.unsigned (N.v49554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49554 s i)) at 1.
  unfold R.v49554, N.v49554.
  unfold R.v6, N.v6.
  rewrite ?node_7001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49555 (s : N.State) (i : N.Inputs) :
  R.v49555 (state s) (inputs i) = Zmod.unsigned (N.v49555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49555 s i)) at 1.
  unfold R.v49555, N.v49555.
  rewrite ?node_49553.
  rewrite ?node_49554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49556 (s : N.State) (i : N.Inputs) :
  R.v49556 (state s) (inputs i) = Zmod.unsigned (N.v49556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49556 s i)) at 1.
  unfold R.v49556, N.v49556.
  unfold R.v16484, N.v16484.
  rewrite ?node_49555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49557 (s : N.State) (i : N.Inputs) :
  R.v49557 (state s) (inputs i) = Zmod.unsigned (N.v49557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49557 s i)) at 1.
  unfold R.v49557, N.v49557.
  rewrite ?node_49550.
  rewrite ?node_49551.
  rewrite ?node_49552.
  rewrite ?node_49556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49558 (s : N.State) (i : N.Inputs) :
  R.v49558 (state s) (inputs i) = Zmod.unsigned (N.v49558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49558 s i)) at 1.
  unfold R.v49558, N.v49558.
  unfold R.v6, N.v6.
  rewrite ?node_49557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49559 (s : N.State) (i : N.Inputs) :
  R.v49559 (state s) (inputs i) = Zmod.unsigned (N.v49559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49559 s i)) at 1.
  unfold R.v49559, N.v49559.
  rewrite ?node_7042.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49560 (s : N.State) (i : N.Inputs) :
  R.v49560 (state s) (inputs i) = Zmod.unsigned (N.v49560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49560 s i)) at 1.
  unfold R.v49560, N.v49560.
  unfold R.v6, N.v6.
  rewrite ?node_7140.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49561 (s : N.State) (i : N.Inputs) :
  R.v49561 (state s) (inputs i) = Zmod.unsigned (N.v49561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49561 s i)) at 1.
  unfold R.v49561, N.v49561.
  unfold R.v6, N.v6.
  rewrite ?node_7152.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49562 (s : N.State) (i : N.Inputs) :
  R.v49562 (state s) (inputs i) = Zmod.unsigned (N.v49562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49562 s i)) at 1.
  unfold R.v49562, N.v49562.
  rewrite ?node_49559.
  rewrite ?node_49560.
  rewrite ?node_49561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49563 (s : N.State) (i : N.Inputs) :
  R.v49563 (state s) (inputs i) = Zmod.unsigned (N.v49563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49563 s i)) at 1.
  unfold R.v49563, N.v49563.
  rewrite ?node_49558.
  rewrite ?node_49562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49564 (s : N.State) (i : N.Inputs) :
  R.v49564 (state s) (inputs i) = Zmod.unsigned (N.v49564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49564 s i)) at 1.
  unfold R.v49564, N.v49564.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49565 (s : N.State) (i : N.Inputs) :
  R.v49565 (state s) (inputs i) = Zmod.unsigned (N.v49565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49565 s i)) at 1.
  unfold R.v49565, N.v49565.
  rewrite ?node_7033.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49566 (s : N.State) (i : N.Inputs) :
  R.v49566 (state s) (inputs i) = Zmod.unsigned (N.v49566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49566 s i)) at 1.
  unfold R.v49566, N.v49566.
  unfold R.v6, N.v6.
  rewrite ?node_7021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49567 (s : N.State) (i : N.Inputs) :
  R.v49567 (state s) (inputs i) = Zmod.unsigned (N.v49567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49567 s i)) at 1.
  unfold R.v49567, N.v49567.
  unfold R.v6, N.v6.
  rewrite ?node_7001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49568 (s : N.State) (i : N.Inputs) :
  R.v49568 (state s) (inputs i) = Zmod.unsigned (N.v49568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49568 s i)) at 1.
  unfold R.v49568, N.v49568.
  rewrite ?node_49566.
  rewrite ?node_49567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49569 (s : N.State) (i : N.Inputs) :
  R.v49569 (state s) (inputs i) = Zmod.unsigned (N.v49569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49569 s i)) at 1.
  unfold R.v49569, N.v49569.
  unfold R.v16484, N.v16484.
  rewrite ?node_49568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49570 (s : N.State) (i : N.Inputs) :
  R.v49570 (state s) (inputs i) = Zmod.unsigned (N.v49570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49570 s i)) at 1.
  unfold R.v49570, N.v49570.
  rewrite ?node_49565.
  rewrite ?node_49569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49571 (s : N.State) (i : N.Inputs) :
  R.v49571 (state s) (inputs i) = Zmod.unsigned (N.v49571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49571 s i)) at 1.
  unfold R.v49571, N.v49571.
  unfold R.v6, N.v6.
  rewrite ?node_49570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49572 (s : N.State) (i : N.Inputs) :
  R.v49572 (state s) (inputs i) = Zmod.unsigned (N.v49572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49572 s i)) at 1.
  unfold R.v49572, N.v49572.
  rewrite ?node_7034.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49573 (s : N.State) (i : N.Inputs) :
  R.v49573 (state s) (inputs i) = Zmod.unsigned (N.v49573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49573 s i)) at 1.
  unfold R.v49573, N.v49573.
  unfold R.v6, N.v6.
  rewrite ?node_7140.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49574 (s : N.State) (i : N.Inputs) :
  R.v49574 (state s) (inputs i) = Zmod.unsigned (N.v49574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49574 s i)) at 1.
  unfold R.v49574, N.v49574.
  rewrite ?node_49572.
  rewrite ?node_49573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49575 (s : N.State) (i : N.Inputs) :
  R.v49575 (state s) (inputs i) = Zmod.unsigned (N.v49575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49575 s i)) at 1.
  unfold R.v49575, N.v49575.
  rewrite ?node_49571.
  rewrite ?node_49574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49576 (s : N.State) (i : N.Inputs) :
  R.v49576 (state s) (inputs i) = Zmod.unsigned (N.v49576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49576 s i)) at 1.
  unfold R.v49576, N.v49576.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49577 (s : N.State) (i : N.Inputs) :
  R.v49577 (state s) (inputs i) = Zmod.unsigned (N.v49577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49577 s i)) at 1.
  unfold R.v49577, N.v49577.
  rewrite ?node_7041.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49578 (s : N.State) (i : N.Inputs) :
  R.v49578 (state s) (inputs i) = Zmod.unsigned (N.v49578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49578 s i)) at 1.
  unfold R.v49578, N.v49578.
  unfold R.v6, N.v6.
  rewrite ?node_7037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49579 (s : N.State) (i : N.Inputs) :
  R.v49579 (state s) (inputs i) = Zmod.unsigned (N.v49579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49579 s i)) at 1.
  unfold R.v49579, N.v49579.
  unfold R.v6, N.v6.
  rewrite ?node_7034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49580 (s : N.State) (i : N.Inputs) :
  R.v49580 (state s) (inputs i) = Zmod.unsigned (N.v49580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49580 s i)) at 1.
  unfold R.v49580, N.v49580.
  rewrite ?node_49578.
  rewrite ?node_49579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49581 (s : N.State) (i : N.Inputs) :
  R.v49581 (state s) (inputs i) = Zmod.unsigned (N.v49581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49581 s i)) at 1.
  unfold R.v49581, N.v49581.
  unfold R.v16484, N.v16484.
  rewrite ?node_49580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49582 (s : N.State) (i : N.Inputs) :
  R.v49582 (state s) (inputs i) = Zmod.unsigned (N.v49582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49582 s i)) at 1.
  unfold R.v49582, N.v49582.
  rewrite ?node_49577.
  rewrite ?node_49581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49583 (s : N.State) (i : N.Inputs) :
  R.v49583 (state s) (inputs i) = Zmod.unsigned (N.v49583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49583 s i)) at 1.
  unfold R.v49583, N.v49583.
  unfold R.v6, N.v6.
  rewrite ?node_49582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49584 (s : N.State) (i : N.Inputs) :
  R.v49584 (state s) (inputs i) = Zmod.unsigned (N.v49584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49584 s i)) at 1.
  unfold R.v49584, N.v49584.
  rewrite ?node_7042.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49585 (s : N.State) (i : N.Inputs) :
  R.v49585 (state s) (inputs i) = Zmod.unsigned (N.v49585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49585 s i)) at 1.
  unfold R.v49585, N.v49585.
  unfold R.v6, N.v6.
  rewrite ?node_7152.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49586 (s : N.State) (i : N.Inputs) :
  R.v49586 (state s) (inputs i) = Zmod.unsigned (N.v49586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49586 s i)) at 1.
  unfold R.v49586, N.v49586.
  rewrite ?node_49584.
  rewrite ?node_49585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49587 (s : N.State) (i : N.Inputs) :
  R.v49587 (state s) (inputs i) = Zmod.unsigned (N.v49587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49587 s i)) at 1.
  unfold R.v49587, N.v49587.
  rewrite ?node_49583.
  rewrite ?node_49586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49588 (s : N.State) (i : N.Inputs) :
  R.v49588 (state s) (inputs i) = Zmod.unsigned (N.v49588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49588 s i)) at 1.
  unfold R.v49588, N.v49588.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49589 (s : N.State) (i : N.Inputs) :
  R.v49589 (state s) (inputs i) = Zmod.unsigned (N.v49589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49589 s i)) at 1.
  unfold R.v49589, N.v49589.
  unfold R.v6, N.v6.
  rewrite ?node_7046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49590 (s : N.State) (i : N.Inputs) :
  R.v49590 (state s) (inputs i) = Zmod.unsigned (N.v49590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49590 s i)) at 1.
  unfold R.v49590, N.v49590.
  unfold R.v6, N.v6.
  rewrite ?node_7045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49591 (s : N.State) (i : N.Inputs) :
  R.v49591 (state s) (inputs i) = Zmod.unsigned (N.v49591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49591 s i)) at 1.
  unfold R.v49591, N.v49591.
  rewrite ?node_49589.
  rewrite ?node_49590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49592 (s : N.State) (i : N.Inputs) :
  R.v49592 (state s) (inputs i) = Zmod.unsigned (N.v49592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49592 s i)) at 1.
  unfold R.v49592, N.v49592.
  unfold R.v16463, N.v16463.
  rewrite ?node_49591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49593 (s : N.State) (i : N.Inputs) :
  R.v49593 (state s) (inputs i) = Zmod.unsigned (N.v49593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49593 s i)) at 1.
  unfold R.v49593, N.v49593.
  rewrite ?node_7047.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49594 (s : N.State) (i : N.Inputs) :
  R.v49594 (state s) (inputs i) = Zmod.unsigned (N.v49594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49594 s i)) at 1.
  unfold R.v49594, N.v49594.
  unfold R.v6, N.v6.
  rewrite ?node_7154.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49595 (s : N.State) (i : N.Inputs) :
  R.v49595 (state s) (inputs i) = Zmod.unsigned (N.v49595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49595 s i)) at 1.
  unfold R.v49595, N.v49595.
  rewrite ?node_49593.
  rewrite ?node_49594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49596 (s : N.State) (i : N.Inputs) :
  R.v49596 (state s) (inputs i) = Zmod.unsigned (N.v49596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49596 s i)) at 1.
  unfold R.v49596, N.v49596.
  rewrite ?node_49592.
  rewrite ?node_49595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49597 (s : N.State) (i : N.Inputs) :
  R.v49597 (state s) (inputs i) = Zmod.unsigned (N.v49597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49597 s i)) at 1.
  unfold R.v49597, N.v49597.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49598 (s : N.State) (i : N.Inputs) :
  R.v49598 (state s) (inputs i) = Zmod.unsigned (N.v49598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49598 s i)) at 1.
  unfold R.v49598, N.v49598.
  rewrite ?node_7140.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49599 (s : N.State) (i : N.Inputs) :
  R.v49599 (state s) (inputs i) = Zmod.unsigned (N.v49599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49599 s i)) at 1.
  unfold R.v49599, N.v49599.
  rewrite ?node_7136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49600 (s : N.State) (i : N.Inputs) :
  R.v49600 (state s) (inputs i) = Zmod.unsigned (N.v49600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49600 s i)) at 1.
  unfold R.v49600, N.v49600.
  rewrite ?node_7132.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49601 (s : N.State) (i : N.Inputs) :
  R.v49601 (state s) (inputs i) = Zmod.unsigned (N.v49601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49601 s i)) at 1.
  unfold R.v49601, N.v49601.
  unfold R.v6, N.v6.
  rewrite ?node_7120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49602 (s : N.State) (i : N.Inputs) :
  R.v49602 (state s) (inputs i) = Zmod.unsigned (N.v49602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49602 s i)) at 1.
  unfold R.v49602, N.v49602.
  unfold R.v6, N.v6.
  rewrite ?node_7100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49603 (s : N.State) (i : N.Inputs) :
  R.v49603 (state s) (inputs i) = Zmod.unsigned (N.v49603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49603 s i)) at 1.
  unfold R.v49603, N.v49603.
  rewrite ?node_49601.
  rewrite ?node_49602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49604 (s : N.State) (i : N.Inputs) :
  R.v49604 (state s) (inputs i) = Zmod.unsigned (N.v49604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49604 s i)) at 1.
  unfold R.v49604, N.v49604.
  unfold R.v16484, N.v16484.
  rewrite ?node_49603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49605 (s : N.State) (i : N.Inputs) :
  R.v49605 (state s) (inputs i) = Zmod.unsigned (N.v49605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49605 s i)) at 1.
  unfold R.v49605, N.v49605.
  rewrite ?node_49598.
  rewrite ?node_49599.
  rewrite ?node_49600.
  rewrite ?node_49604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49606 (s : N.State) (i : N.Inputs) :
  R.v49606 (state s) (inputs i) = Zmod.unsigned (N.v49606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49606 s i)) at 1.
  unfold R.v49606, N.v49606.
  unfold R.v6, N.v6.
  rewrite ?node_49605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49607 (s : N.State) (i : N.Inputs) :
  R.v49607 (state s) (inputs i) = Zmod.unsigned (N.v49607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49607 s i)) at 1.
  unfold R.v49607, N.v49607.
  rewrite ?node_7141.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49608 (s : N.State) (i : N.Inputs) :
  R.v49608 (state s) (inputs i) = Zmod.unsigned (N.v49608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49608 s i)) at 1.
  unfold R.v49608, N.v49608.
  unfold R.v6, N.v6.
  rewrite ?node_7242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49609 (s : N.State) (i : N.Inputs) :
  R.v49609 (state s) (inputs i) = Zmod.unsigned (N.v49609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49609 s i)) at 1.
  unfold R.v49609, N.v49609.
  unfold R.v6, N.v6.
  rewrite ?node_7254.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49610 (s : N.State) (i : N.Inputs) :
  R.v49610 (state s) (inputs i) = Zmod.unsigned (N.v49610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49610 s i)) at 1.
  unfold R.v49610, N.v49610.
  rewrite ?node_49607.
  rewrite ?node_49608.
  rewrite ?node_49609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49611 (s : N.State) (i : N.Inputs) :
  R.v49611 (state s) (inputs i) = Zmod.unsigned (N.v49611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49611 s i)) at 1.
  unfold R.v49611, N.v49611.
  rewrite ?node_49606.
  rewrite ?node_49610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49612 (s : N.State) (i : N.Inputs) :
  R.v49612 (state s) (inputs i) = Zmod.unsigned (N.v49612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49612 s i)) at 1.
  unfold R.v49612, N.v49612.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49613 (s : N.State) (i : N.Inputs) :
  R.v49613 (state s) (inputs i) = Zmod.unsigned (N.v49613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49613 s i)) at 1.
  unfold R.v49613, N.v49613.
  rewrite ?node_7132.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49614 (s : N.State) (i : N.Inputs) :
  R.v49614 (state s) (inputs i) = Zmod.unsigned (N.v49614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49614 s i)) at 1.
  unfold R.v49614, N.v49614.
  unfold R.v6, N.v6.
  rewrite ?node_7120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49615 (s : N.State) (i : N.Inputs) :
  R.v49615 (state s) (inputs i) = Zmod.unsigned (N.v49615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49615 s i)) at 1.
  unfold R.v49615, N.v49615.
  unfold R.v6, N.v6.
  rewrite ?node_7100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49616 (s : N.State) (i : N.Inputs) :
  R.v49616 (state s) (inputs i) = Zmod.unsigned (N.v49616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49616 s i)) at 1.
  unfold R.v49616, N.v49616.
  rewrite ?node_49614.
  rewrite ?node_49615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49617 (s : N.State) (i : N.Inputs) :
  R.v49617 (state s) (inputs i) = Zmod.unsigned (N.v49617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49617 s i)) at 1.
  unfold R.v49617, N.v49617.
  unfold R.v16484, N.v16484.
  rewrite ?node_49616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49618 (s : N.State) (i : N.Inputs) :
  R.v49618 (state s) (inputs i) = Zmod.unsigned (N.v49618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49618 s i)) at 1.
  unfold R.v49618, N.v49618.
  rewrite ?node_49613.
  rewrite ?node_49617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49619 (s : N.State) (i : N.Inputs) :
  R.v49619 (state s) (inputs i) = Zmod.unsigned (N.v49619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49619 s i)) at 1.
  unfold R.v49619, N.v49619.
  unfold R.v6, N.v6.
  rewrite ?node_49618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49620 (s : N.State) (i : N.Inputs) :
  R.v49620 (state s) (inputs i) = Zmod.unsigned (N.v49620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49620 s i)) at 1.
  unfold R.v49620, N.v49620.
  rewrite ?node_7133.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49621 (s : N.State) (i : N.Inputs) :
  R.v49621 (state s) (inputs i) = Zmod.unsigned (N.v49621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49621 s i)) at 1.
  unfold R.v49621, N.v49621.
  unfold R.v6, N.v6.
  rewrite ?node_7242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49622 (s : N.State) (i : N.Inputs) :
  R.v49622 (state s) (inputs i) = Zmod.unsigned (N.v49622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49622 s i)) at 1.
  unfold R.v49622, N.v49622.
  rewrite ?node_49620.
  rewrite ?node_49621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49623 (s : N.State) (i : N.Inputs) :
  R.v49623 (state s) (inputs i) = Zmod.unsigned (N.v49623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49623 s i)) at 1.
  unfold R.v49623, N.v49623.
  rewrite ?node_49619.
  rewrite ?node_49622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49624 (s : N.State) (i : N.Inputs) :
  R.v49624 (state s) (inputs i) = Zmod.unsigned (N.v49624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49624 s i)) at 1.
  unfold R.v49624, N.v49624.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49625 (s : N.State) (i : N.Inputs) :
  R.v49625 (state s) (inputs i) = Zmod.unsigned (N.v49625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49625 s i)) at 1.
  unfold R.v49625, N.v49625.
  rewrite ?node_7140.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49626 (s : N.State) (i : N.Inputs) :
  R.v49626 (state s) (inputs i) = Zmod.unsigned (N.v49626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49626 s i)) at 1.
  unfold R.v49626, N.v49626.
  unfold R.v6, N.v6.
  rewrite ?node_7136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49627 (s : N.State) (i : N.Inputs) :
  R.v49627 (state s) (inputs i) = Zmod.unsigned (N.v49627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49627 s i)) at 1.
  unfold R.v49627, N.v49627.
  unfold R.v6, N.v6.
  rewrite ?node_7133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49628 (s : N.State) (i : N.Inputs) :
  R.v49628 (state s) (inputs i) = Zmod.unsigned (N.v49628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49628 s i)) at 1.
  unfold R.v49628, N.v49628.
  rewrite ?node_49626.
  rewrite ?node_49627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49629 (s : N.State) (i : N.Inputs) :
  R.v49629 (state s) (inputs i) = Zmod.unsigned (N.v49629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49629 s i)) at 1.
  unfold R.v49629, N.v49629.
  unfold R.v16484, N.v16484.
  rewrite ?node_49628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49630 (s : N.State) (i : N.Inputs) :
  R.v49630 (state s) (inputs i) = Zmod.unsigned (N.v49630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49630 s i)) at 1.
  unfold R.v49630, N.v49630.
  rewrite ?node_49625.
  rewrite ?node_49629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49631 (s : N.State) (i : N.Inputs) :
  R.v49631 (state s) (inputs i) = Zmod.unsigned (N.v49631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49631 s i)) at 1.
  unfold R.v49631, N.v49631.
  unfold R.v6, N.v6.
  rewrite ?node_49630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49632 (s : N.State) (i : N.Inputs) :
  R.v49632 (state s) (inputs i) = Zmod.unsigned (N.v49632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49632 s i)) at 1.
  unfold R.v49632, N.v49632.
  rewrite ?node_7141.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49633 (s : N.State) (i : N.Inputs) :
  R.v49633 (state s) (inputs i) = Zmod.unsigned (N.v49633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49633 s i)) at 1.
  unfold R.v49633, N.v49633.
  unfold R.v6, N.v6.
  rewrite ?node_7254.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49634 (s : N.State) (i : N.Inputs) :
  R.v49634 (state s) (inputs i) = Zmod.unsigned (N.v49634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49634 s i)) at 1.
  unfold R.v49634, N.v49634.
  rewrite ?node_49632.
  rewrite ?node_49633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49635 (s : N.State) (i : N.Inputs) :
  R.v49635 (state s) (inputs i) = Zmod.unsigned (N.v49635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49635 s i)) at 1.
  unfold R.v49635, N.v49635.
  rewrite ?node_49631.
  rewrite ?node_49634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49636 (s : N.State) (i : N.Inputs) :
  R.v49636 (state s) (inputs i) = Zmod.unsigned (N.v49636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49636 s i)) at 1.
  unfold R.v49636, N.v49636.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49637 (s : N.State) (i : N.Inputs) :
  R.v49637 (state s) (inputs i) = Zmod.unsigned (N.v49637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49637 s i)) at 1.
  unfold R.v49637, N.v49637.
  unfold R.v6, N.v6.
  rewrite ?node_7147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49638 (s : N.State) (i : N.Inputs) :
  R.v49638 (state s) (inputs i) = Zmod.unsigned (N.v49638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49638 s i)) at 1.
  unfold R.v49638, N.v49638.
  unfold R.v6, N.v6.
  rewrite ?node_7144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49639 (s : N.State) (i : N.Inputs) :
  R.v49639 (state s) (inputs i) = Zmod.unsigned (N.v49639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49639 s i)) at 1.
  unfold R.v49639, N.v49639.
  rewrite ?node_49637.
  rewrite ?node_49638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49640 (s : N.State) (i : N.Inputs) :
  R.v49640 (state s) (inputs i) = Zmod.unsigned (N.v49640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49640 s i)) at 1.
  unfold R.v49640, N.v49640.
  unfold R.v16463, N.v16463.
  rewrite ?node_49639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49641 (s : N.State) (i : N.Inputs) :
  R.v49641 (state s) (inputs i) = Zmod.unsigned (N.v49641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49641 s i)) at 1.
  unfold R.v49641, N.v49641.
  rewrite ?node_7148.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49642 (s : N.State) (i : N.Inputs) :
  R.v49642 (state s) (inputs i) = Zmod.unsigned (N.v49642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49642 s i)) at 1.
  unfold R.v49642, N.v49642.
  unfold R.v6, N.v6.
  rewrite ?node_7256.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49643 (s : N.State) (i : N.Inputs) :
  R.v49643 (state s) (inputs i) = Zmod.unsigned (N.v49643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49643 s i)) at 1.
  unfold R.v49643, N.v49643.
  rewrite ?node_49641.
  rewrite ?node_49642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49644 (s : N.State) (i : N.Inputs) :
  R.v49644 (state s) (inputs i) = Zmod.unsigned (N.v49644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49644 s i)) at 1.
  unfold R.v49644, N.v49644.
  rewrite ?node_49640.
  rewrite ?node_49643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49645 (s : N.State) (i : N.Inputs) :
  R.v49645 (state s) (inputs i) = Zmod.unsigned (N.v49645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49645 s i)) at 1.
  unfold R.v49645, N.v49645.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49646 (s : N.State) (i : N.Inputs) :
  R.v49646 (state s) (inputs i) = Zmod.unsigned (N.v49646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49646 s i)) at 1.
  unfold R.v49646, N.v49646.
  rewrite ?node_7242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49647 (s : N.State) (i : N.Inputs) :
  R.v49647 (state s) (inputs i) = Zmod.unsigned (N.v49647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49647 s i)) at 1.
  unfold R.v49647, N.v49647.
  rewrite ?node_7238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49648 (s : N.State) (i : N.Inputs) :
  R.v49648 (state s) (inputs i) = Zmod.unsigned (N.v49648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49648 s i)) at 1.
  unfold R.v49648, N.v49648.
  rewrite ?node_7234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49649 (s : N.State) (i : N.Inputs) :
  R.v49649 (state s) (inputs i) = Zmod.unsigned (N.v49649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49649 s i)) at 1.
  unfold R.v49649, N.v49649.
  unfold R.v6, N.v6.
  rewrite ?node_7222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49650 (s : N.State) (i : N.Inputs) :
  R.v49650 (state s) (inputs i) = Zmod.unsigned (N.v49650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49650 s i)) at 1.
  unfold R.v49650, N.v49650.
  unfold R.v6, N.v6.
  rewrite ?node_7201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49651 (s : N.State) (i : N.Inputs) :
  R.v49651 (state s) (inputs i) = Zmod.unsigned (N.v49651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49651 s i)) at 1.
  unfold R.v49651, N.v49651.
  rewrite ?node_49649.
  rewrite ?node_49650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49652 (s : N.State) (i : N.Inputs) :
  R.v49652 (state s) (inputs i) = Zmod.unsigned (N.v49652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49652 s i)) at 1.
  unfold R.v49652, N.v49652.
  unfold R.v16484, N.v16484.
  rewrite ?node_49651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49653 (s : N.State) (i : N.Inputs) :
  R.v49653 (state s) (inputs i) = Zmod.unsigned (N.v49653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49653 s i)) at 1.
  unfold R.v49653, N.v49653.
  rewrite ?node_49646.
  rewrite ?node_49647.
  rewrite ?node_49648.
  rewrite ?node_49652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49654 (s : N.State) (i : N.Inputs) :
  R.v49654 (state s) (inputs i) = Zmod.unsigned (N.v49654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49654 s i)) at 1.
  unfold R.v49654, N.v49654.
  unfold R.v6, N.v6.
  rewrite ?node_49653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49655 (s : N.State) (i : N.Inputs) :
  R.v49655 (state s) (inputs i) = Zmod.unsigned (N.v49655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49655 s i)) at 1.
  unfold R.v49655, N.v49655.
  rewrite ?node_7243.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49656 (s : N.State) (i : N.Inputs) :
  R.v49656 (state s) (inputs i) = Zmod.unsigned (N.v49656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49656 s i)) at 1.
  unfold R.v49656, N.v49656.
  unfold R.v6, N.v6.
  rewrite ?node_7346.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49657 (s : N.State) (i : N.Inputs) :
  R.v49657 (state s) (inputs i) = Zmod.unsigned (N.v49657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49657 s i)) at 1.
  unfold R.v49657, N.v49657.
  unfold R.v6, N.v6.
  rewrite ?node_7358.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49658 (s : N.State) (i : N.Inputs) :
  R.v49658 (state s) (inputs i) = Zmod.unsigned (N.v49658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49658 s i)) at 1.
  unfold R.v49658, N.v49658.
  rewrite ?node_49655.
  rewrite ?node_49656.
  rewrite ?node_49657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49659 (s : N.State) (i : N.Inputs) :
  R.v49659 (state s) (inputs i) = Zmod.unsigned (N.v49659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49659 s i)) at 1.
  unfold R.v49659, N.v49659.
  rewrite ?node_49654.
  rewrite ?node_49658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49660 (s : N.State) (i : N.Inputs) :
  R.v49660 (state s) (inputs i) = Zmod.unsigned (N.v49660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49660 s i)) at 1.
  unfold R.v49660, N.v49660.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49661 (s : N.State) (i : N.Inputs) :
  R.v49661 (state s) (inputs i) = Zmod.unsigned (N.v49661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49661 s i)) at 1.
  unfold R.v49661, N.v49661.
  rewrite ?node_7234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49662 (s : N.State) (i : N.Inputs) :
  R.v49662 (state s) (inputs i) = Zmod.unsigned (N.v49662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49662 s i)) at 1.
  unfold R.v49662, N.v49662.
  unfold R.v6, N.v6.
  rewrite ?node_7222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49663 (s : N.State) (i : N.Inputs) :
  R.v49663 (state s) (inputs i) = Zmod.unsigned (N.v49663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49663 s i)) at 1.
  unfold R.v49663, N.v49663.
  unfold R.v6, N.v6.
  rewrite ?node_7201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49664 (s : N.State) (i : N.Inputs) :
  R.v49664 (state s) (inputs i) = Zmod.unsigned (N.v49664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49664 s i)) at 1.
  unfold R.v49664, N.v49664.
  rewrite ?node_49662.
  rewrite ?node_49663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49665 (s : N.State) (i : N.Inputs) :
  R.v49665 (state s) (inputs i) = Zmod.unsigned (N.v49665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49665 s i)) at 1.
  unfold R.v49665, N.v49665.
  unfold R.v16484, N.v16484.
  rewrite ?node_49664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49666 (s : N.State) (i : N.Inputs) :
  R.v49666 (state s) (inputs i) = Zmod.unsigned (N.v49666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49666 s i)) at 1.
  unfold R.v49666, N.v49666.
  rewrite ?node_49661.
  rewrite ?node_49665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49667 (s : N.State) (i : N.Inputs) :
  R.v49667 (state s) (inputs i) = Zmod.unsigned (N.v49667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49667 s i)) at 1.
  unfold R.v49667, N.v49667.
  unfold R.v6, N.v6.
  rewrite ?node_49666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49668 (s : N.State) (i : N.Inputs) :
  R.v49668 (state s) (inputs i) = Zmod.unsigned (N.v49668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49668 s i)) at 1.
  unfold R.v49668, N.v49668.
  rewrite ?node_7235.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49669 (s : N.State) (i : N.Inputs) :
  R.v49669 (state s) (inputs i) = Zmod.unsigned (N.v49669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49669 s i)) at 1.
  unfold R.v49669, N.v49669.
  unfold R.v6, N.v6.
  rewrite ?node_7346.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49670 (s : N.State) (i : N.Inputs) :
  R.v49670 (state s) (inputs i) = Zmod.unsigned (N.v49670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49670 s i)) at 1.
  unfold R.v49670, N.v49670.
  rewrite ?node_49668.
  rewrite ?node_49669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49671 (s : N.State) (i : N.Inputs) :
  R.v49671 (state s) (inputs i) = Zmod.unsigned (N.v49671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49671 s i)) at 1.
  unfold R.v49671, N.v49671.
  rewrite ?node_49667.
  rewrite ?node_49670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49672 (s : N.State) (i : N.Inputs) :
  R.v49672 (state s) (inputs i) = Zmod.unsigned (N.v49672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49672 s i)) at 1.
  unfold R.v49672, N.v49672.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49673 (s : N.State) (i : N.Inputs) :
  R.v49673 (state s) (inputs i) = Zmod.unsigned (N.v49673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49673 s i)) at 1.
  unfold R.v49673, N.v49673.
  rewrite ?node_7242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49674 (s : N.State) (i : N.Inputs) :
  R.v49674 (state s) (inputs i) = Zmod.unsigned (N.v49674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49674 s i)) at 1.
  unfold R.v49674, N.v49674.
  unfold R.v6, N.v6.
  rewrite ?node_7238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49675 (s : N.State) (i : N.Inputs) :
  R.v49675 (state s) (inputs i) = Zmod.unsigned (N.v49675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49675 s i)) at 1.
  unfold R.v49675, N.v49675.
  unfold R.v6, N.v6.
  rewrite ?node_7235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49676 (s : N.State) (i : N.Inputs) :
  R.v49676 (state s) (inputs i) = Zmod.unsigned (N.v49676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49676 s i)) at 1.
  unfold R.v49676, N.v49676.
  rewrite ?node_49674.
  rewrite ?node_49675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49677 (s : N.State) (i : N.Inputs) :
  R.v49677 (state s) (inputs i) = Zmod.unsigned (N.v49677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49677 s i)) at 1.
  unfold R.v49677, N.v49677.
  unfold R.v16484, N.v16484.
  rewrite ?node_49676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49678 (s : N.State) (i : N.Inputs) :
  R.v49678 (state s) (inputs i) = Zmod.unsigned (N.v49678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49678 s i)) at 1.
  unfold R.v49678, N.v49678.
  rewrite ?node_49673.
  rewrite ?node_49677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49679 (s : N.State) (i : N.Inputs) :
  R.v49679 (state s) (inputs i) = Zmod.unsigned (N.v49679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49679 s i)) at 1.
  unfold R.v49679, N.v49679.
  unfold R.v6, N.v6.
  rewrite ?node_49678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49680 (s : N.State) (i : N.Inputs) :
  R.v49680 (state s) (inputs i) = Zmod.unsigned (N.v49680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49680 s i)) at 1.
  unfold R.v49680, N.v49680.
  rewrite ?node_7243.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49681 (s : N.State) (i : N.Inputs) :
  R.v49681 (state s) (inputs i) = Zmod.unsigned (N.v49681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49681 s i)) at 1.
  unfold R.v49681, N.v49681.
  unfold R.v6, N.v6.
  rewrite ?node_7358.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49682 (s : N.State) (i : N.Inputs) :
  R.v49682 (state s) (inputs i) = Zmod.unsigned (N.v49682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49682 s i)) at 1.
  unfold R.v49682, N.v49682.
  rewrite ?node_49680.
  rewrite ?node_49681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49683 (s : N.State) (i : N.Inputs) :
  R.v49683 (state s) (inputs i) = Zmod.unsigned (N.v49683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49683 s i)) at 1.
  unfold R.v49683, N.v49683.
  rewrite ?node_49679.
  rewrite ?node_49682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49684 (s : N.State) (i : N.Inputs) :
  R.v49684 (state s) (inputs i) = Zmod.unsigned (N.v49684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49684 s i)) at 1.
  unfold R.v49684, N.v49684.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49685 (s : N.State) (i : N.Inputs) :
  R.v49685 (state s) (inputs i) = Zmod.unsigned (N.v49685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49685 s i)) at 1.
  unfold R.v49685, N.v49685.
  unfold R.v6, N.v6.
  rewrite ?node_7249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49686 (s : N.State) (i : N.Inputs) :
  R.v49686 (state s) (inputs i) = Zmod.unsigned (N.v49686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49686 s i)) at 1.
  unfold R.v49686, N.v49686.
  unfold R.v6, N.v6.
  rewrite ?node_7246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49687 (s : N.State) (i : N.Inputs) :
  R.v49687 (state s) (inputs i) = Zmod.unsigned (N.v49687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49687 s i)) at 1.
  unfold R.v49687, N.v49687.
  rewrite ?node_49685.
  rewrite ?node_49686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49688 (s : N.State) (i : N.Inputs) :
  R.v49688 (state s) (inputs i) = Zmod.unsigned (N.v49688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49688 s i)) at 1.
  unfold R.v49688, N.v49688.
  unfold R.v16463, N.v16463.
  rewrite ?node_49687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49689 (s : N.State) (i : N.Inputs) :
  R.v49689 (state s) (inputs i) = Zmod.unsigned (N.v49689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49689 s i)) at 1.
  unfold R.v49689, N.v49689.
  rewrite ?node_7250.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49690 (s : N.State) (i : N.Inputs) :
  R.v49690 (state s) (inputs i) = Zmod.unsigned (N.v49690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49690 s i)) at 1.
  unfold R.v49690, N.v49690.
  unfold R.v6, N.v6.
  rewrite ?node_7360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49691 (s : N.State) (i : N.Inputs) :
  R.v49691 (state s) (inputs i) = Zmod.unsigned (N.v49691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49691 s i)) at 1.
  unfold R.v49691, N.v49691.
  rewrite ?node_49689.
  rewrite ?node_49690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49692 (s : N.State) (i : N.Inputs) :
  R.v49692 (state s) (inputs i) = Zmod.unsigned (N.v49692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49692 s i)) at 1.
  unfold R.v49692, N.v49692.
  rewrite ?node_49688.
  rewrite ?node_49691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49693 (s : N.State) (i : N.Inputs) :
  R.v49693 (state s) (inputs i) = Zmod.unsigned (N.v49693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49693 s i)) at 1.
  unfold R.v49693, N.v49693.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49694 (s : N.State) (i : N.Inputs) :
  R.v49694 (state s) (inputs i) = Zmod.unsigned (N.v49694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49694 s i)) at 1.
  unfold R.v49694, N.v49694.
  rewrite ?node_7346.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49695 (s : N.State) (i : N.Inputs) :
  R.v49695 (state s) (inputs i) = Zmod.unsigned (N.v49695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49695 s i)) at 1.
  unfold R.v49695, N.v49695.
  rewrite ?node_7342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49696 (s : N.State) (i : N.Inputs) :
  R.v49696 (state s) (inputs i) = Zmod.unsigned (N.v49696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49696 s i)) at 1.
  unfold R.v49696, N.v49696.
  rewrite ?node_7338.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49697 (s : N.State) (i : N.Inputs) :
  R.v49697 (state s) (inputs i) = Zmod.unsigned (N.v49697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49697 s i)) at 1.
  unfold R.v49697, N.v49697.
  unfold R.v6, N.v6.
  rewrite ?node_7324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49698 (s : N.State) (i : N.Inputs) :
  R.v49698 (state s) (inputs i) = Zmod.unsigned (N.v49698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49698 s i)) at 1.
  unfold R.v49698, N.v49698.
  unfold R.v6, N.v6.
  rewrite ?node_7303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49699 (s : N.State) (i : N.Inputs) :
  R.v49699 (state s) (inputs i) = Zmod.unsigned (N.v49699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49699 s i)) at 1.
  unfold R.v49699, N.v49699.
  rewrite ?node_49697.
  rewrite ?node_49698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49700 (s : N.State) (i : N.Inputs) :
  R.v49700 (state s) (inputs i) = Zmod.unsigned (N.v49700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49700 s i)) at 1.
  unfold R.v49700, N.v49700.
  unfold R.v16484, N.v16484.
  rewrite ?node_49699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49701 (s : N.State) (i : N.Inputs) :
  R.v49701 (state s) (inputs i) = Zmod.unsigned (N.v49701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49701 s i)) at 1.
  unfold R.v49701, N.v49701.
  rewrite ?node_49694.
  rewrite ?node_49695.
  rewrite ?node_49696.
  rewrite ?node_49700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49702 (s : N.State) (i : N.Inputs) :
  R.v49702 (state s) (inputs i) = Zmod.unsigned (N.v49702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49702 s i)) at 1.
  unfold R.v49702, N.v49702.
  unfold R.v6, N.v6.
  rewrite ?node_49701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49703 (s : N.State) (i : N.Inputs) :
  R.v49703 (state s) (inputs i) = Zmod.unsigned (N.v49703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49703 s i)) at 1.
  unfold R.v49703, N.v49703.
  rewrite ?node_7347.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49704 (s : N.State) (i : N.Inputs) :
  R.v49704 (state s) (inputs i) = Zmod.unsigned (N.v49704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49704 s i)) at 1.
  unfold R.v49704, N.v49704.
  unfold R.v6, N.v6.
  rewrite ?node_7455.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49705 (s : N.State) (i : N.Inputs) :
  R.v49705 (state s) (inputs i) = Zmod.unsigned (N.v49705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49705 s i)) at 1.
  unfold R.v49705, N.v49705.
  unfold R.v6, N.v6.
  rewrite ?node_7465.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49706 (s : N.State) (i : N.Inputs) :
  R.v49706 (state s) (inputs i) = Zmod.unsigned (N.v49706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49706 s i)) at 1.
  unfold R.v49706, N.v49706.
  rewrite ?node_49703.
  rewrite ?node_49704.
  rewrite ?node_49705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49707 (s : N.State) (i : N.Inputs) :
  R.v49707 (state s) (inputs i) = Zmod.unsigned (N.v49707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49707 s i)) at 1.
  unfold R.v49707, N.v49707.
  rewrite ?node_49702.
  rewrite ?node_49706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49708 (s : N.State) (i : N.Inputs) :
  R.v49708 (state s) (inputs i) = Zmod.unsigned (N.v49708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49708 s i)) at 1.
  unfold R.v49708, N.v49708.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49709 (s : N.State) (i : N.Inputs) :
  R.v49709 (state s) (inputs i) = Zmod.unsigned (N.v49709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49709 s i)) at 1.
  unfold R.v49709, N.v49709.
  rewrite ?node_7338.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49710 (s : N.State) (i : N.Inputs) :
  R.v49710 (state s) (inputs i) = Zmod.unsigned (N.v49710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49710 s i)) at 1.
  unfold R.v49710, N.v49710.
  unfold R.v6, N.v6.
  rewrite ?node_7324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49711 (s : N.State) (i : N.Inputs) :
  R.v49711 (state s) (inputs i) = Zmod.unsigned (N.v49711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49711 s i)) at 1.
  unfold R.v49711, N.v49711.
  unfold R.v6, N.v6.
  rewrite ?node_7303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49712 (s : N.State) (i : N.Inputs) :
  R.v49712 (state s) (inputs i) = Zmod.unsigned (N.v49712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49712 s i)) at 1.
  unfold R.v49712, N.v49712.
  rewrite ?node_49710.
  rewrite ?node_49711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49713 (s : N.State) (i : N.Inputs) :
  R.v49713 (state s) (inputs i) = Zmod.unsigned (N.v49713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49713 s i)) at 1.
  unfold R.v49713, N.v49713.
  unfold R.v16484, N.v16484.
  rewrite ?node_49712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49714 (s : N.State) (i : N.Inputs) :
  R.v49714 (state s) (inputs i) = Zmod.unsigned (N.v49714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49714 s i)) at 1.
  unfold R.v49714, N.v49714.
  rewrite ?node_49709.
  rewrite ?node_49713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49715 (s : N.State) (i : N.Inputs) :
  R.v49715 (state s) (inputs i) = Zmod.unsigned (N.v49715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49715 s i)) at 1.
  unfold R.v49715, N.v49715.
  unfold R.v6, N.v6.
  rewrite ?node_49714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49716 (s : N.State) (i : N.Inputs) :
  R.v49716 (state s) (inputs i) = Zmod.unsigned (N.v49716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49716 s i)) at 1.
  unfold R.v49716, N.v49716.
  rewrite ?node_7339.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49717 (s : N.State) (i : N.Inputs) :
  R.v49717 (state s) (inputs i) = Zmod.unsigned (N.v49717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49717 s i)) at 1.
  unfold R.v49717, N.v49717.
  unfold R.v6, N.v6.
  rewrite ?node_7455.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49718 (s : N.State) (i : N.Inputs) :
  R.v49718 (state s) (inputs i) = Zmod.unsigned (N.v49718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49718 s i)) at 1.
  unfold R.v49718, N.v49718.
  rewrite ?node_49716.
  rewrite ?node_49717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49719 (s : N.State) (i : N.Inputs) :
  R.v49719 (state s) (inputs i) = Zmod.unsigned (N.v49719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49719 s i)) at 1.
  unfold R.v49719, N.v49719.
  rewrite ?node_49715.
  rewrite ?node_49718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49720 (s : N.State) (i : N.Inputs) :
  R.v49720 (state s) (inputs i) = Zmod.unsigned (N.v49720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49720 s i)) at 1.
  unfold R.v49720, N.v49720.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49721 (s : N.State) (i : N.Inputs) :
  R.v49721 (state s) (inputs i) = Zmod.unsigned (N.v49721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49721 s i)) at 1.
  unfold R.v49721, N.v49721.
  rewrite ?node_7346.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49722 (s : N.State) (i : N.Inputs) :
  R.v49722 (state s) (inputs i) = Zmod.unsigned (N.v49722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49722 s i)) at 1.
  unfold R.v49722, N.v49722.
  unfold R.v6, N.v6.
  rewrite ?node_7342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49723 (s : N.State) (i : N.Inputs) :
  R.v49723 (state s) (inputs i) = Zmod.unsigned (N.v49723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49723 s i)) at 1.
  unfold R.v49723, N.v49723.
  unfold R.v6, N.v6.
  rewrite ?node_7339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49724 (s : N.State) (i : N.Inputs) :
  R.v49724 (state s) (inputs i) = Zmod.unsigned (N.v49724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49724 s i)) at 1.
  unfold R.v49724, N.v49724.
  rewrite ?node_49722.
  rewrite ?node_49723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49725 (s : N.State) (i : N.Inputs) :
  R.v49725 (state s) (inputs i) = Zmod.unsigned (N.v49725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49725 s i)) at 1.
  unfold R.v49725, N.v49725.
  unfold R.v16484, N.v16484.
  rewrite ?node_49724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49726 (s : N.State) (i : N.Inputs) :
  R.v49726 (state s) (inputs i) = Zmod.unsigned (N.v49726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49726 s i)) at 1.
  unfold R.v49726, N.v49726.
  rewrite ?node_49721.
  rewrite ?node_49725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49727 (s : N.State) (i : N.Inputs) :
  R.v49727 (state s) (inputs i) = Zmod.unsigned (N.v49727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49727 s i)) at 1.
  unfold R.v49727, N.v49727.
  unfold R.v6, N.v6.
  rewrite ?node_49726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49728 (s : N.State) (i : N.Inputs) :
  R.v49728 (state s) (inputs i) = Zmod.unsigned (N.v49728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49728 s i)) at 1.
  unfold R.v49728, N.v49728.
  rewrite ?node_7347.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49729 (s : N.State) (i : N.Inputs) :
  R.v49729 (state s) (inputs i) = Zmod.unsigned (N.v49729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49729 s i)) at 1.
  unfold R.v49729, N.v49729.
  unfold R.v6, N.v6.
  rewrite ?node_7465.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49730 (s : N.State) (i : N.Inputs) :
  R.v49730 (state s) (inputs i) = Zmod.unsigned (N.v49730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49730 s i)) at 1.
  unfold R.v49730, N.v49730.
  rewrite ?node_49728.
  rewrite ?node_49729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49731 (s : N.State) (i : N.Inputs) :
  R.v49731 (state s) (inputs i) = Zmod.unsigned (N.v49731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49731 s i)) at 1.
  unfold R.v49731, N.v49731.
  rewrite ?node_49727.
  rewrite ?node_49730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49732 (s : N.State) (i : N.Inputs) :
  R.v49732 (state s) (inputs i) = Zmod.unsigned (N.v49732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49732 s i)) at 1.
  unfold R.v49732, N.v49732.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49733 (s : N.State) (i : N.Inputs) :
  R.v49733 (state s) (inputs i) = Zmod.unsigned (N.v49733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49733 s i)) at 1.
  unfold R.v49733, N.v49733.
  unfold R.v6, N.v6.
  rewrite ?node_7353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49734 (s : N.State) (i : N.Inputs) :
  R.v49734 (state s) (inputs i) = Zmod.unsigned (N.v49734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49734 s i)) at 1.
  unfold R.v49734, N.v49734.
  unfold R.v6, N.v6.
  rewrite ?node_7350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49735 (s : N.State) (i : N.Inputs) :
  R.v49735 (state s) (inputs i) = Zmod.unsigned (N.v49735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49735 s i)) at 1.
  unfold R.v49735, N.v49735.
  rewrite ?node_49733.
  rewrite ?node_49734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49736 (s : N.State) (i : N.Inputs) :
  R.v49736 (state s) (inputs i) = Zmod.unsigned (N.v49736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49736 s i)) at 1.
  unfold R.v49736, N.v49736.
  unfold R.v16463, N.v16463.
  rewrite ?node_49735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49737 (s : N.State) (i : N.Inputs) :
  R.v49737 (state s) (inputs i) = Zmod.unsigned (N.v49737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49737 s i)) at 1.
  unfold R.v49737, N.v49737.
  rewrite ?node_7354.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49738 (s : N.State) (i : N.Inputs) :
  R.v49738 (state s) (inputs i) = Zmod.unsigned (N.v49738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49738 s i)) at 1.
  unfold R.v49738, N.v49738.
  unfold R.v6, N.v6.
  rewrite ?node_7467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49739 (s : N.State) (i : N.Inputs) :
  R.v49739 (state s) (inputs i) = Zmod.unsigned (N.v49739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49739 s i)) at 1.
  unfold R.v49739, N.v49739.
  rewrite ?node_49737.
  rewrite ?node_49738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49740 (s : N.State) (i : N.Inputs) :
  R.v49740 (state s) (inputs i) = Zmod.unsigned (N.v49740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49740 s i)) at 1.
  unfold R.v49740, N.v49740.
  rewrite ?node_49736.
  rewrite ?node_49739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49741 (s : N.State) (i : N.Inputs) :
  R.v49741 (state s) (inputs i) = Zmod.unsigned (N.v49741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49741 s i)) at 1.
  unfold R.v49741, N.v49741.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49742 (s : N.State) (i : N.Inputs) :
  R.v49742 (state s) (inputs i) = Zmod.unsigned (N.v49742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49742 s i)) at 1.
  unfold R.v49742, N.v49742.
  rewrite ?node_7455.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49743 (s : N.State) (i : N.Inputs) :
  R.v49743 (state s) (inputs i) = Zmod.unsigned (N.v49743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49743 s i)) at 1.
  unfold R.v49743, N.v49743.
  rewrite ?node_7451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49744 (s : N.State) (i : N.Inputs) :
  R.v49744 (state s) (inputs i) = Zmod.unsigned (N.v49744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49744 s i)) at 1.
  unfold R.v49744, N.v49744.
  rewrite ?node_7447.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49745 (s : N.State) (i : N.Inputs) :
  R.v49745 (state s) (inputs i) = Zmod.unsigned (N.v49745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49745 s i)) at 1.
  unfold R.v49745, N.v49745.
  unfold R.v6, N.v6.
  rewrite ?node_7429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49746 (s : N.State) (i : N.Inputs) :
  R.v49746 (state s) (inputs i) = Zmod.unsigned (N.v49746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49746 s i)) at 1.
  unfold R.v49746, N.v49746.
  unfold R.v6, N.v6.
  rewrite ?node_7407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49747 (s : N.State) (i : N.Inputs) :
  R.v49747 (state s) (inputs i) = Zmod.unsigned (N.v49747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49747 s i)) at 1.
  unfold R.v49747, N.v49747.
  rewrite ?node_49745.
  rewrite ?node_49746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49748 (s : N.State) (i : N.Inputs) :
  R.v49748 (state s) (inputs i) = Zmod.unsigned (N.v49748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49748 s i)) at 1.
  unfold R.v49748, N.v49748.
  unfold R.v16484, N.v16484.
  rewrite ?node_49747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49749 (s : N.State) (i : N.Inputs) :
  R.v49749 (state s) (inputs i) = Zmod.unsigned (N.v49749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49749 s i)) at 1.
  unfold R.v49749, N.v49749.
  rewrite ?node_49742.
  rewrite ?node_49743.
  rewrite ?node_49744.
  rewrite ?node_49748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49750 (s : N.State) (i : N.Inputs) :
  R.v49750 (state s) (inputs i) = Zmod.unsigned (N.v49750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49750 s i)) at 1.
  unfold R.v49750, N.v49750.
  unfold R.v6, N.v6.
  rewrite ?node_49749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49751 (s : N.State) (i : N.Inputs) :
  R.v49751 (state s) (inputs i) = Zmod.unsigned (N.v49751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49751 s i)) at 1.
  unfold R.v49751, N.v49751.
  rewrite ?node_7456.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49752 (s : N.State) (i : N.Inputs) :
  R.v49752 (state s) (inputs i) = Zmod.unsigned (N.v49752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49752 s i)) at 1.
  unfold R.v49752, N.v49752.
  unfold R.v6, N.v6.
  rewrite ?node_7564.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49753 (s : N.State) (i : N.Inputs) :
  R.v49753 (state s) (inputs i) = Zmod.unsigned (N.v49753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49753 s i)) at 1.
  unfold R.v49753, N.v49753.
  unfold R.v6, N.v6.
  rewrite ?node_7576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49754 (s : N.State) (i : N.Inputs) :
  R.v49754 (state s) (inputs i) = Zmod.unsigned (N.v49754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49754 s i)) at 1.
  unfold R.v49754, N.v49754.
  rewrite ?node_49751.
  rewrite ?node_49752.
  rewrite ?node_49753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49755 (s : N.State) (i : N.Inputs) :
  R.v49755 (state s) (inputs i) = Zmod.unsigned (N.v49755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49755 s i)) at 1.
  unfold R.v49755, N.v49755.
  rewrite ?node_49750.
  rewrite ?node_49754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49756 (s : N.State) (i : N.Inputs) :
  R.v49756 (state s) (inputs i) = Zmod.unsigned (N.v49756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49756 s i)) at 1.
  unfold R.v49756, N.v49756.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49757 (s : N.State) (i : N.Inputs) :
  R.v49757 (state s) (inputs i) = Zmod.unsigned (N.v49757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49757 s i)) at 1.
  unfold R.v49757, N.v49757.
  rewrite ?node_7447.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49758 (s : N.State) (i : N.Inputs) :
  R.v49758 (state s) (inputs i) = Zmod.unsigned (N.v49758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49758 s i)) at 1.
  unfold R.v49758, N.v49758.
  unfold R.v6, N.v6.
  rewrite ?node_7429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49759 (s : N.State) (i : N.Inputs) :
  R.v49759 (state s) (inputs i) = Zmod.unsigned (N.v49759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49759 s i)) at 1.
  unfold R.v49759, N.v49759.
  unfold R.v6, N.v6.
  rewrite ?node_7407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49760 (s : N.State) (i : N.Inputs) :
  R.v49760 (state s) (inputs i) = Zmod.unsigned (N.v49760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49760 s i)) at 1.
  unfold R.v49760, N.v49760.
  rewrite ?node_49758.
  rewrite ?node_49759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49761 (s : N.State) (i : N.Inputs) :
  R.v49761 (state s) (inputs i) = Zmod.unsigned (N.v49761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49761 s i)) at 1.
  unfold R.v49761, N.v49761.
  unfold R.v16484, N.v16484.
  rewrite ?node_49760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49762 (s : N.State) (i : N.Inputs) :
  R.v49762 (state s) (inputs i) = Zmod.unsigned (N.v49762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49762 s i)) at 1.
  unfold R.v49762, N.v49762.
  rewrite ?node_49757.
  rewrite ?node_49761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49763 (s : N.State) (i : N.Inputs) :
  R.v49763 (state s) (inputs i) = Zmod.unsigned (N.v49763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49763 s i)) at 1.
  unfold R.v49763, N.v49763.
  unfold R.v6, N.v6.
  rewrite ?node_49762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49764 (s : N.State) (i : N.Inputs) :
  R.v49764 (state s) (inputs i) = Zmod.unsigned (N.v49764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49764 s i)) at 1.
  unfold R.v49764, N.v49764.
  rewrite ?node_7448.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49765 (s : N.State) (i : N.Inputs) :
  R.v49765 (state s) (inputs i) = Zmod.unsigned (N.v49765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49765 s i)) at 1.
  unfold R.v49765, N.v49765.
  unfold R.v6, N.v6.
  rewrite ?node_7564.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49766 (s : N.State) (i : N.Inputs) :
  R.v49766 (state s) (inputs i) = Zmod.unsigned (N.v49766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49766 s i)) at 1.
  unfold R.v49766, N.v49766.
  rewrite ?node_49764.
  rewrite ?node_49765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49767 (s : N.State) (i : N.Inputs) :
  R.v49767 (state s) (inputs i) = Zmod.unsigned (N.v49767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49767 s i)) at 1.
  unfold R.v49767, N.v49767.
  rewrite ?node_49763.
  rewrite ?node_49766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49768 (s : N.State) (i : N.Inputs) :
  R.v49768 (state s) (inputs i) = Zmod.unsigned (N.v49768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49768 s i)) at 1.
  unfold R.v49768, N.v49768.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49769 (s : N.State) (i : N.Inputs) :
  R.v49769 (state s) (inputs i) = Zmod.unsigned (N.v49769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49769 s i)) at 1.
  unfold R.v49769, N.v49769.
  rewrite ?node_7455.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49770 (s : N.State) (i : N.Inputs) :
  R.v49770 (state s) (inputs i) = Zmod.unsigned (N.v49770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49770 s i)) at 1.
  unfold R.v49770, N.v49770.
  unfold R.v6, N.v6.
  rewrite ?node_7451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49771 (s : N.State) (i : N.Inputs) :
  R.v49771 (state s) (inputs i) = Zmod.unsigned (N.v49771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49771 s i)) at 1.
  unfold R.v49771, N.v49771.
  unfold R.v6, N.v6.
  rewrite ?node_7448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49772 (s : N.State) (i : N.Inputs) :
  R.v49772 (state s) (inputs i) = Zmod.unsigned (N.v49772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49772 s i)) at 1.
  unfold R.v49772, N.v49772.
  rewrite ?node_49770.
  rewrite ?node_49771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49773 (s : N.State) (i : N.Inputs) :
  R.v49773 (state s) (inputs i) = Zmod.unsigned (N.v49773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49773 s i)) at 1.
  unfold R.v49773, N.v49773.
  unfold R.v16484, N.v16484.
  rewrite ?node_49772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49774 (s : N.State) (i : N.Inputs) :
  R.v49774 (state s) (inputs i) = Zmod.unsigned (N.v49774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49774 s i)) at 1.
  unfold R.v49774, N.v49774.
  rewrite ?node_49769.
  rewrite ?node_49773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49775 (s : N.State) (i : N.Inputs) :
  R.v49775 (state s) (inputs i) = Zmod.unsigned (N.v49775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49775 s i)) at 1.
  unfold R.v49775, N.v49775.
  unfold R.v6, N.v6.
  rewrite ?node_49774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49776 (s : N.State) (i : N.Inputs) :
  R.v49776 (state s) (inputs i) = Zmod.unsigned (N.v49776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49776 s i)) at 1.
  unfold R.v49776, N.v49776.
  rewrite ?node_7456.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49777 (s : N.State) (i : N.Inputs) :
  R.v49777 (state s) (inputs i) = Zmod.unsigned (N.v49777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49777 s i)) at 1.
  unfold R.v49777, N.v49777.
  unfold R.v6, N.v6.
  rewrite ?node_7576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49778 (s : N.State) (i : N.Inputs) :
  R.v49778 (state s) (inputs i) = Zmod.unsigned (N.v49778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49778 s i)) at 1.
  unfold R.v49778, N.v49778.
  rewrite ?node_49776.
  rewrite ?node_49777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49779 (s : N.State) (i : N.Inputs) :
  R.v49779 (state s) (inputs i) = Zmod.unsigned (N.v49779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49779 s i)) at 1.
  unfold R.v49779, N.v49779.
  rewrite ?node_49775.
  rewrite ?node_49778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49780 (s : N.State) (i : N.Inputs) :
  R.v49780 (state s) (inputs i) = Zmod.unsigned (N.v49780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49780 s i)) at 1.
  unfold R.v49780, N.v49780.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49781 (s : N.State) (i : N.Inputs) :
  R.v49781 (state s) (inputs i) = Zmod.unsigned (N.v49781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49781 s i)) at 1.
  unfold R.v49781, N.v49781.
  unfold R.v6, N.v6.
  rewrite ?node_7460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49782 (s : N.State) (i : N.Inputs) :
  R.v49782 (state s) (inputs i) = Zmod.unsigned (N.v49782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49782 s i)) at 1.
  unfold R.v49782, N.v49782.
  unfold R.v6, N.v6.
  rewrite ?node_7459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49783 (s : N.State) (i : N.Inputs) :
  R.v49783 (state s) (inputs i) = Zmod.unsigned (N.v49783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49783 s i)) at 1.
  unfold R.v49783, N.v49783.
  rewrite ?node_49781.
  rewrite ?node_49782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49784 (s : N.State) (i : N.Inputs) :
  R.v49784 (state s) (inputs i) = Zmod.unsigned (N.v49784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49784 s i)) at 1.
  unfold R.v49784, N.v49784.
  unfold R.v16463, N.v16463.
  rewrite ?node_49783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49785 (s : N.State) (i : N.Inputs) :
  R.v49785 (state s) (inputs i) = Zmod.unsigned (N.v49785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49785 s i)) at 1.
  unfold R.v49785, N.v49785.
  rewrite ?node_7461.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49786 (s : N.State) (i : N.Inputs) :
  R.v49786 (state s) (inputs i) = Zmod.unsigned (N.v49786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49786 s i)) at 1.
  unfold R.v49786, N.v49786.
  unfold R.v6, N.v6.
  rewrite ?node_7578.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49787 (s : N.State) (i : N.Inputs) :
  R.v49787 (state s) (inputs i) = Zmod.unsigned (N.v49787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49787 s i)) at 1.
  unfold R.v49787, N.v49787.
  rewrite ?node_49785.
  rewrite ?node_49786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49788 (s : N.State) (i : N.Inputs) :
  R.v49788 (state s) (inputs i) = Zmod.unsigned (N.v49788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49788 s i)) at 1.
  unfold R.v49788, N.v49788.
  rewrite ?node_49784.
  rewrite ?node_49787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49789 (s : N.State) (i : N.Inputs) :
  R.v49789 (state s) (inputs i) = Zmod.unsigned (N.v49789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49789 s i)) at 1.
  unfold R.v49789, N.v49789.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49790 (s : N.State) (i : N.Inputs) :
  R.v49790 (state s) (inputs i) = Zmod.unsigned (N.v49790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49790 s i)) at 1.
  unfold R.v49790, N.v49790.
  rewrite ?node_7564.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49791 (s : N.State) (i : N.Inputs) :
  R.v49791 (state s) (inputs i) = Zmod.unsigned (N.v49791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49791 s i)) at 1.
  unfold R.v49791, N.v49791.
  rewrite ?node_7560.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49792 (s : N.State) (i : N.Inputs) :
  R.v49792 (state s) (inputs i) = Zmod.unsigned (N.v49792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49792 s i)) at 1.
  unfold R.v49792, N.v49792.
  rewrite ?node_7556.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49793 (s : N.State) (i : N.Inputs) :
  R.v49793 (state s) (inputs i) = Zmod.unsigned (N.v49793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49793 s i)) at 1.
  unfold R.v49793, N.v49793.
  unfold R.v6, N.v6.
  rewrite ?node_7536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49794 (s : N.State) (i : N.Inputs) :
  R.v49794 (state s) (inputs i) = Zmod.unsigned (N.v49794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49794 s i)) at 1.
  unfold R.v49794, N.v49794.
  unfold R.v6, N.v6.
  rewrite ?node_7514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49795 (s : N.State) (i : N.Inputs) :
  R.v49795 (state s) (inputs i) = Zmod.unsigned (N.v49795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49795 s i)) at 1.
  unfold R.v49795, N.v49795.
  rewrite ?node_49793.
  rewrite ?node_49794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49796 (s : N.State) (i : N.Inputs) :
  R.v49796 (state s) (inputs i) = Zmod.unsigned (N.v49796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49796 s i)) at 1.
  unfold R.v49796, N.v49796.
  unfold R.v16484, N.v16484.
  rewrite ?node_49795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49797 (s : N.State) (i : N.Inputs) :
  R.v49797 (state s) (inputs i) = Zmod.unsigned (N.v49797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49797 s i)) at 1.
  unfold R.v49797, N.v49797.
  rewrite ?node_49790.
  rewrite ?node_49791.
  rewrite ?node_49792.
  rewrite ?node_49796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49798 (s : N.State) (i : N.Inputs) :
  R.v49798 (state s) (inputs i) = Zmod.unsigned (N.v49798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49798 s i)) at 1.
  unfold R.v49798, N.v49798.
  unfold R.v6, N.v6.
  rewrite ?node_49797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49799 (s : N.State) (i : N.Inputs) :
  R.v49799 (state s) (inputs i) = Zmod.unsigned (N.v49799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49799 s i)) at 1.
  unfold R.v49799, N.v49799.
  rewrite ?node_7565.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49800 (s : N.State) (i : N.Inputs) :
  R.v49800 (state s) (inputs i) = Zmod.unsigned (N.v49800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49800 s i)) at 1.
  unfold R.v49800, N.v49800.
  unfold R.v6, N.v6.
  rewrite ?node_7676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49801 (s : N.State) (i : N.Inputs) :
  R.v49801 (state s) (inputs i) = Zmod.unsigned (N.v49801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49801 s i)) at 1.
  unfold R.v49801, N.v49801.
  unfold R.v6, N.v6.
  rewrite ?node_7688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49802 (s : N.State) (i : N.Inputs) :
  R.v49802 (state s) (inputs i) = Zmod.unsigned (N.v49802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49802 s i)) at 1.
  unfold R.v49802, N.v49802.
  rewrite ?node_49799.
  rewrite ?node_49800.
  rewrite ?node_49801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49803 (s : N.State) (i : N.Inputs) :
  R.v49803 (state s) (inputs i) = Zmod.unsigned (N.v49803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49803 s i)) at 1.
  unfold R.v49803, N.v49803.
  rewrite ?node_49798.
  rewrite ?node_49802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49804 (s : N.State) (i : N.Inputs) :
  R.v49804 (state s) (inputs i) = Zmod.unsigned (N.v49804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49804 s i)) at 1.
  unfold R.v49804, N.v49804.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49805 (s : N.State) (i : N.Inputs) :
  R.v49805 (state s) (inputs i) = Zmod.unsigned (N.v49805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49805 s i)) at 1.
  unfold R.v49805, N.v49805.
  rewrite ?node_7556.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49806 (s : N.State) (i : N.Inputs) :
  R.v49806 (state s) (inputs i) = Zmod.unsigned (N.v49806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49806 s i)) at 1.
  unfold R.v49806, N.v49806.
  unfold R.v6, N.v6.
  rewrite ?node_7536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49807 (s : N.State) (i : N.Inputs) :
  R.v49807 (state s) (inputs i) = Zmod.unsigned (N.v49807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49807 s i)) at 1.
  unfold R.v49807, N.v49807.
  unfold R.v6, N.v6.
  rewrite ?node_7514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49808 (s : N.State) (i : N.Inputs) :
  R.v49808 (state s) (inputs i) = Zmod.unsigned (N.v49808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49808 s i)) at 1.
  unfold R.v49808, N.v49808.
  rewrite ?node_49806.
  rewrite ?node_49807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49809 (s : N.State) (i : N.Inputs) :
  R.v49809 (state s) (inputs i) = Zmod.unsigned (N.v49809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49809 s i)) at 1.
  unfold R.v49809, N.v49809.
  unfold R.v16484, N.v16484.
  rewrite ?node_49808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49810 (s : N.State) (i : N.Inputs) :
  R.v49810 (state s) (inputs i) = Zmod.unsigned (N.v49810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49810 s i)) at 1.
  unfold R.v49810, N.v49810.
  rewrite ?node_49805.
  rewrite ?node_49809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49811 (s : N.State) (i : N.Inputs) :
  R.v49811 (state s) (inputs i) = Zmod.unsigned (N.v49811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49811 s i)) at 1.
  unfold R.v49811, N.v49811.
  unfold R.v6, N.v6.
  rewrite ?node_49810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49812 (s : N.State) (i : N.Inputs) :
  R.v49812 (state s) (inputs i) = Zmod.unsigned (N.v49812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49812 s i)) at 1.
  unfold R.v49812, N.v49812.
  rewrite ?node_7557.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49813 (s : N.State) (i : N.Inputs) :
  R.v49813 (state s) (inputs i) = Zmod.unsigned (N.v49813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49813 s i)) at 1.
  unfold R.v49813, N.v49813.
  unfold R.v6, N.v6.
  rewrite ?node_7676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49814 (s : N.State) (i : N.Inputs) :
  R.v49814 (state s) (inputs i) = Zmod.unsigned (N.v49814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49814 s i)) at 1.
  unfold R.v49814, N.v49814.
  rewrite ?node_49812.
  rewrite ?node_49813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49815 (s : N.State) (i : N.Inputs) :
  R.v49815 (state s) (inputs i) = Zmod.unsigned (N.v49815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49815 s i)) at 1.
  unfold R.v49815, N.v49815.
  rewrite ?node_49811.
  rewrite ?node_49814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49816 (s : N.State) (i : N.Inputs) :
  R.v49816 (state s) (inputs i) = Zmod.unsigned (N.v49816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49816 s i)) at 1.
  unfold R.v49816, N.v49816.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49817 (s : N.State) (i : N.Inputs) :
  R.v49817 (state s) (inputs i) = Zmod.unsigned (N.v49817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49817 s i)) at 1.
  unfold R.v49817, N.v49817.
  rewrite ?node_7564.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49818 (s : N.State) (i : N.Inputs) :
  R.v49818 (state s) (inputs i) = Zmod.unsigned (N.v49818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49818 s i)) at 1.
  unfold R.v49818, N.v49818.
  unfold R.v6, N.v6.
  rewrite ?node_7560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49819 (s : N.State) (i : N.Inputs) :
  R.v49819 (state s) (inputs i) = Zmod.unsigned (N.v49819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49819 s i)) at 1.
  unfold R.v49819, N.v49819.
  unfold R.v6, N.v6.
  rewrite ?node_7557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49820 (s : N.State) (i : N.Inputs) :
  R.v49820 (state s) (inputs i) = Zmod.unsigned (N.v49820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49820 s i)) at 1.
  unfold R.v49820, N.v49820.
  rewrite ?node_49818.
  rewrite ?node_49819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49821 (s : N.State) (i : N.Inputs) :
  R.v49821 (state s) (inputs i) = Zmod.unsigned (N.v49821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49821 s i)) at 1.
  unfold R.v49821, N.v49821.
  unfold R.v16484, N.v16484.
  rewrite ?node_49820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49822 (s : N.State) (i : N.Inputs) :
  R.v49822 (state s) (inputs i) = Zmod.unsigned (N.v49822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49822 s i)) at 1.
  unfold R.v49822, N.v49822.
  rewrite ?node_49817.
  rewrite ?node_49821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49823 (s : N.State) (i : N.Inputs) :
  R.v49823 (state s) (inputs i) = Zmod.unsigned (N.v49823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49823 s i)) at 1.
  unfold R.v49823, N.v49823.
  unfold R.v6, N.v6.
  rewrite ?node_49822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49824 (s : N.State) (i : N.Inputs) :
  R.v49824 (state s) (inputs i) = Zmod.unsigned (N.v49824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49824 s i)) at 1.
  unfold R.v49824, N.v49824.
  rewrite ?node_7565.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49825 (s : N.State) (i : N.Inputs) :
  R.v49825 (state s) (inputs i) = Zmod.unsigned (N.v49825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49825 s i)) at 1.
  unfold R.v49825, N.v49825.
  unfold R.v6, N.v6.
  rewrite ?node_7688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49826 (s : N.State) (i : N.Inputs) :
  R.v49826 (state s) (inputs i) = Zmod.unsigned (N.v49826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49826 s i)) at 1.
  unfold R.v49826, N.v49826.
  rewrite ?node_49824.
  rewrite ?node_49825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49827 (s : N.State) (i : N.Inputs) :
  R.v49827 (state s) (inputs i) = Zmod.unsigned (N.v49827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49827 s i)) at 1.
  unfold R.v49827, N.v49827.
  rewrite ?node_49823.
  rewrite ?node_49826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49828 (s : N.State) (i : N.Inputs) :
  R.v49828 (state s) (inputs i) = Zmod.unsigned (N.v49828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49828 s i)) at 1.
  unfold R.v49828, N.v49828.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49829 (s : N.State) (i : N.Inputs) :
  R.v49829 (state s) (inputs i) = Zmod.unsigned (N.v49829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49829 s i)) at 1.
  unfold R.v49829, N.v49829.
  unfold R.v6, N.v6.
  rewrite ?node_7571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49830 (s : N.State) (i : N.Inputs) :
  R.v49830 (state s) (inputs i) = Zmod.unsigned (N.v49830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49830 s i)) at 1.
  unfold R.v49830, N.v49830.
  unfold R.v6, N.v6.
  rewrite ?node_7568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49831 (s : N.State) (i : N.Inputs) :
  R.v49831 (state s) (inputs i) = Zmod.unsigned (N.v49831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49831 s i)) at 1.
  unfold R.v49831, N.v49831.
  rewrite ?node_49829.
  rewrite ?node_49830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49832 (s : N.State) (i : N.Inputs) :
  R.v49832 (state s) (inputs i) = Zmod.unsigned (N.v49832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49832 s i)) at 1.
  unfold R.v49832, N.v49832.
  unfold R.v16463, N.v16463.
  rewrite ?node_49831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49833 (s : N.State) (i : N.Inputs) :
  R.v49833 (state s) (inputs i) = Zmod.unsigned (N.v49833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49833 s i)) at 1.
  unfold R.v49833, N.v49833.
  rewrite ?node_7572.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49834 (s : N.State) (i : N.Inputs) :
  R.v49834 (state s) (inputs i) = Zmod.unsigned (N.v49834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49834 s i)) at 1.
  unfold R.v49834, N.v49834.
  unfold R.v6, N.v6.
  rewrite ?node_7690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49835 (s : N.State) (i : N.Inputs) :
  R.v49835 (state s) (inputs i) = Zmod.unsigned (N.v49835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49835 s i)) at 1.
  unfold R.v49835, N.v49835.
  rewrite ?node_49833.
  rewrite ?node_49834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49836 (s : N.State) (i : N.Inputs) :
  R.v49836 (state s) (inputs i) = Zmod.unsigned (N.v49836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49836 s i)) at 1.
  unfold R.v49836, N.v49836.
  rewrite ?node_49832.
  rewrite ?node_49835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49837 (s : N.State) (i : N.Inputs) :
  R.v49837 (state s) (inputs i) = Zmod.unsigned (N.v49837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49837 s i)) at 1.
  unfold R.v49837, N.v49837.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49838 (s : N.State) (i : N.Inputs) :
  R.v49838 (state s) (inputs i) = Zmod.unsigned (N.v49838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49838 s i)) at 1.
  unfold R.v49838, N.v49838.
  rewrite ?node_7676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49839 (s : N.State) (i : N.Inputs) :
  R.v49839 (state s) (inputs i) = Zmod.unsigned (N.v49839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49839 s i)) at 1.
  unfold R.v49839, N.v49839.
  rewrite ?node_7672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49840 (s : N.State) (i : N.Inputs) :
  R.v49840 (state s) (inputs i) = Zmod.unsigned (N.v49840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49840 s i)) at 1.
  unfold R.v49840, N.v49840.
  rewrite ?node_7668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49841 (s : N.State) (i : N.Inputs) :
  R.v49841 (state s) (inputs i) = Zmod.unsigned (N.v49841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49841 s i)) at 1.
  unfold R.v49841, N.v49841.
  unfold R.v6, N.v6.
  rewrite ?node_7648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49842 (s : N.State) (i : N.Inputs) :
  R.v49842 (state s) (inputs i) = Zmod.unsigned (N.v49842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49842 s i)) at 1.
  unfold R.v49842, N.v49842.
  unfold R.v6, N.v6.
  rewrite ?node_7625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49843 (s : N.State) (i : N.Inputs) :
  R.v49843 (state s) (inputs i) = Zmod.unsigned (N.v49843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49843 s i)) at 1.
  unfold R.v49843, N.v49843.
  rewrite ?node_49841.
  rewrite ?node_49842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49844 (s : N.State) (i : N.Inputs) :
  R.v49844 (state s) (inputs i) = Zmod.unsigned (N.v49844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49844 s i)) at 1.
  unfold R.v49844, N.v49844.
  unfold R.v16484, N.v16484.
  rewrite ?node_49843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49845 (s : N.State) (i : N.Inputs) :
  R.v49845 (state s) (inputs i) = Zmod.unsigned (N.v49845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49845 s i)) at 1.
  unfold R.v49845, N.v49845.
  rewrite ?node_49838.
  rewrite ?node_49839.
  rewrite ?node_49840.
  rewrite ?node_49844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49846 (s : N.State) (i : N.Inputs) :
  R.v49846 (state s) (inputs i) = Zmod.unsigned (N.v49846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49846 s i)) at 1.
  unfold R.v49846, N.v49846.
  unfold R.v6, N.v6.
  rewrite ?node_49845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49847 (s : N.State) (i : N.Inputs) :
  R.v49847 (state s) (inputs i) = Zmod.unsigned (N.v49847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49847 s i)) at 1.
  unfold R.v49847, N.v49847.
  rewrite ?node_7677.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49848 (s : N.State) (i : N.Inputs) :
  R.v49848 (state s) (inputs i) = Zmod.unsigned (N.v49848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49848 s i)) at 1.
  unfold R.v49848, N.v49848.
  unfold R.v6, N.v6.
  rewrite ?node_7790.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49849 (s : N.State) (i : N.Inputs) :
  R.v49849 (state s) (inputs i) = Zmod.unsigned (N.v49849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49849 s i)) at 1.
  unfold R.v49849, N.v49849.
  unfold R.v6, N.v6.
  rewrite ?node_7802.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49850 (s : N.State) (i : N.Inputs) :
  R.v49850 (state s) (inputs i) = Zmod.unsigned (N.v49850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49850 s i)) at 1.
  unfold R.v49850, N.v49850.
  rewrite ?node_49847.
  rewrite ?node_49848.
  rewrite ?node_49849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49851 (s : N.State) (i : N.Inputs) :
  R.v49851 (state s) (inputs i) = Zmod.unsigned (N.v49851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49851 s i)) at 1.
  unfold R.v49851, N.v49851.
  rewrite ?node_49846.
  rewrite ?node_49850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49852 (s : N.State) (i : N.Inputs) :
  R.v49852 (state s) (inputs i) = Zmod.unsigned (N.v49852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49852 s i)) at 1.
  unfold R.v49852, N.v49852.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49853 (s : N.State) (i : N.Inputs) :
  R.v49853 (state s) (inputs i) = Zmod.unsigned (N.v49853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49853 s i)) at 1.
  unfold R.v49853, N.v49853.
  rewrite ?node_7668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49854 (s : N.State) (i : N.Inputs) :
  R.v49854 (state s) (inputs i) = Zmod.unsigned (N.v49854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49854 s i)) at 1.
  unfold R.v49854, N.v49854.
  unfold R.v6, N.v6.
  rewrite ?node_7648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49855 (s : N.State) (i : N.Inputs) :
  R.v49855 (state s) (inputs i) = Zmod.unsigned (N.v49855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49855 s i)) at 1.
  unfold R.v49855, N.v49855.
  unfold R.v6, N.v6.
  rewrite ?node_7625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49856 (s : N.State) (i : N.Inputs) :
  R.v49856 (state s) (inputs i) = Zmod.unsigned (N.v49856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49856 s i)) at 1.
  unfold R.v49856, N.v49856.
  rewrite ?node_49854.
  rewrite ?node_49855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49857 (s : N.State) (i : N.Inputs) :
  R.v49857 (state s) (inputs i) = Zmod.unsigned (N.v49857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49857 s i)) at 1.
  unfold R.v49857, N.v49857.
  unfold R.v16484, N.v16484.
  rewrite ?node_49856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49858 (s : N.State) (i : N.Inputs) :
  R.v49858 (state s) (inputs i) = Zmod.unsigned (N.v49858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49858 s i)) at 1.
  unfold R.v49858, N.v49858.
  rewrite ?node_49853.
  rewrite ?node_49857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49859 (s : N.State) (i : N.Inputs) :
  R.v49859 (state s) (inputs i) = Zmod.unsigned (N.v49859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49859 s i)) at 1.
  unfold R.v49859, N.v49859.
  unfold R.v6, N.v6.
  rewrite ?node_49858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49860 (s : N.State) (i : N.Inputs) :
  R.v49860 (state s) (inputs i) = Zmod.unsigned (N.v49860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49860 s i)) at 1.
  unfold R.v49860, N.v49860.
  rewrite ?node_7669.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49861 (s : N.State) (i : N.Inputs) :
  R.v49861 (state s) (inputs i) = Zmod.unsigned (N.v49861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49861 s i)) at 1.
  unfold R.v49861, N.v49861.
  unfold R.v6, N.v6.
  rewrite ?node_7790.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49862 (s : N.State) (i : N.Inputs) :
  R.v49862 (state s) (inputs i) = Zmod.unsigned (N.v49862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49862 s i)) at 1.
  unfold R.v49862, N.v49862.
  rewrite ?node_49860.
  rewrite ?node_49861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49863 (s : N.State) (i : N.Inputs) :
  R.v49863 (state s) (inputs i) = Zmod.unsigned (N.v49863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49863 s i)) at 1.
  unfold R.v49863, N.v49863.
  rewrite ?node_49859.
  rewrite ?node_49862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49864 (s : N.State) (i : N.Inputs) :
  R.v49864 (state s) (inputs i) = Zmod.unsigned (N.v49864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49864 s i)) at 1.
  unfold R.v49864, N.v49864.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49865 (s : N.State) (i : N.Inputs) :
  R.v49865 (state s) (inputs i) = Zmod.unsigned (N.v49865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49865 s i)) at 1.
  unfold R.v49865, N.v49865.
  rewrite ?node_7676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49866 (s : N.State) (i : N.Inputs) :
  R.v49866 (state s) (inputs i) = Zmod.unsigned (N.v49866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49866 s i)) at 1.
  unfold R.v49866, N.v49866.
  unfold R.v6, N.v6.
  rewrite ?node_7672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49867 (s : N.State) (i : N.Inputs) :
  R.v49867 (state s) (inputs i) = Zmod.unsigned (N.v49867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49867 s i)) at 1.
  unfold R.v49867, N.v49867.
  unfold R.v6, N.v6.
  rewrite ?node_7669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49868 (s : N.State) (i : N.Inputs) :
  R.v49868 (state s) (inputs i) = Zmod.unsigned (N.v49868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49868 s i)) at 1.
  unfold R.v49868, N.v49868.
  rewrite ?node_49866.
  rewrite ?node_49867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49869 (s : N.State) (i : N.Inputs) :
  R.v49869 (state s) (inputs i) = Zmod.unsigned (N.v49869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49869 s i)) at 1.
  unfold R.v49869, N.v49869.
  unfold R.v16484, N.v16484.
  rewrite ?node_49868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49870 (s : N.State) (i : N.Inputs) :
  R.v49870 (state s) (inputs i) = Zmod.unsigned (N.v49870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49870 s i)) at 1.
  unfold R.v49870, N.v49870.
  rewrite ?node_49865.
  rewrite ?node_49869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49871 (s : N.State) (i : N.Inputs) :
  R.v49871 (state s) (inputs i) = Zmod.unsigned (N.v49871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49871 s i)) at 1.
  unfold R.v49871, N.v49871.
  unfold R.v6, N.v6.
  rewrite ?node_49870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49872 (s : N.State) (i : N.Inputs) :
  R.v49872 (state s) (inputs i) = Zmod.unsigned (N.v49872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49872 s i)) at 1.
  unfold R.v49872, N.v49872.
  rewrite ?node_7677.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49873 (s : N.State) (i : N.Inputs) :
  R.v49873 (state s) (inputs i) = Zmod.unsigned (N.v49873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49873 s i)) at 1.
  unfold R.v49873, N.v49873.
  unfold R.v6, N.v6.
  rewrite ?node_7802.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49874 (s : N.State) (i : N.Inputs) :
  R.v49874 (state s) (inputs i) = Zmod.unsigned (N.v49874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49874 s i)) at 1.
  unfold R.v49874, N.v49874.
  rewrite ?node_49872.
  rewrite ?node_49873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49875 (s : N.State) (i : N.Inputs) :
  R.v49875 (state s) (inputs i) = Zmod.unsigned (N.v49875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49875 s i)) at 1.
  unfold R.v49875, N.v49875.
  rewrite ?node_49871.
  rewrite ?node_49874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49876 (s : N.State) (i : N.Inputs) :
  R.v49876 (state s) (inputs i) = Zmod.unsigned (N.v49876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49876 s i)) at 1.
  unfold R.v49876, N.v49876.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49877 (s : N.State) (i : N.Inputs) :
  R.v49877 (state s) (inputs i) = Zmod.unsigned (N.v49877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49877 s i)) at 1.
  unfold R.v49877, N.v49877.
  unfold R.v6, N.v6.
  rewrite ?node_7683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49878 (s : N.State) (i : N.Inputs) :
  R.v49878 (state s) (inputs i) = Zmod.unsigned (N.v49878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49878 s i)) at 1.
  unfold R.v49878, N.v49878.
  unfold R.v6, N.v6.
  rewrite ?node_7680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49879 (s : N.State) (i : N.Inputs) :
  R.v49879 (state s) (inputs i) = Zmod.unsigned (N.v49879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49879 s i)) at 1.
  unfold R.v49879, N.v49879.
  rewrite ?node_49877.
  rewrite ?node_49878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49880 (s : N.State) (i : N.Inputs) :
  R.v49880 (state s) (inputs i) = Zmod.unsigned (N.v49880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49880 s i)) at 1.
  unfold R.v49880, N.v49880.
  unfold R.v16463, N.v16463.
  rewrite ?node_49879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49881 (s : N.State) (i : N.Inputs) :
  R.v49881 (state s) (inputs i) = Zmod.unsigned (N.v49881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49881 s i)) at 1.
  unfold R.v49881, N.v49881.
  rewrite ?node_7684.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49882 (s : N.State) (i : N.Inputs) :
  R.v49882 (state s) (inputs i) = Zmod.unsigned (N.v49882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49882 s i)) at 1.
  unfold R.v49882, N.v49882.
  unfold R.v6, N.v6.
  rewrite ?node_7804.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49883 (s : N.State) (i : N.Inputs) :
  R.v49883 (state s) (inputs i) = Zmod.unsigned (N.v49883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49883 s i)) at 1.
  unfold R.v49883, N.v49883.
  rewrite ?node_49881.
  rewrite ?node_49882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49884 (s : N.State) (i : N.Inputs) :
  R.v49884 (state s) (inputs i) = Zmod.unsigned (N.v49884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49884 s i)) at 1.
  unfold R.v49884, N.v49884.
  rewrite ?node_49880.
  rewrite ?node_49883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49885 (s : N.State) (i : N.Inputs) :
  R.v49885 (state s) (inputs i) = Zmod.unsigned (N.v49885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49885 s i)) at 1.
  unfold R.v49885, N.v49885.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49886 (s : N.State) (i : N.Inputs) :
  R.v49886 (state s) (inputs i) = Zmod.unsigned (N.v49886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49886 s i)) at 1.
  unfold R.v49886, N.v49886.
  rewrite ?node_7790.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49887 (s : N.State) (i : N.Inputs) :
  R.v49887 (state s) (inputs i) = Zmod.unsigned (N.v49887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49887 s i)) at 1.
  unfold R.v49887, N.v49887.
  rewrite ?node_7786.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49888 (s : N.State) (i : N.Inputs) :
  R.v49888 (state s) (inputs i) = Zmod.unsigned (N.v49888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49888 s i)) at 1.
  unfold R.v49888, N.v49888.
  rewrite ?node_7782.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49889 (s : N.State) (i : N.Inputs) :
  R.v49889 (state s) (inputs i) = Zmod.unsigned (N.v49889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49889 s i)) at 1.
  unfold R.v49889, N.v49889.
  unfold R.v6, N.v6.
  rewrite ?node_7764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49890 (s : N.State) (i : N.Inputs) :
  R.v49890 (state s) (inputs i) = Zmod.unsigned (N.v49890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49890 s i)) at 1.
  unfold R.v49890, N.v49890.
  unfold R.v6, N.v6.
  rewrite ?node_7737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49891 (s : N.State) (i : N.Inputs) :
  R.v49891 (state s) (inputs i) = Zmod.unsigned (N.v49891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49891 s i)) at 1.
  unfold R.v49891, N.v49891.
  rewrite ?node_49889.
  rewrite ?node_49890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49892 (s : N.State) (i : N.Inputs) :
  R.v49892 (state s) (inputs i) = Zmod.unsigned (N.v49892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49892 s i)) at 1.
  unfold R.v49892, N.v49892.
  unfold R.v16484, N.v16484.
  rewrite ?node_49891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49893 (s : N.State) (i : N.Inputs) :
  R.v49893 (state s) (inputs i) = Zmod.unsigned (N.v49893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49893 s i)) at 1.
  unfold R.v49893, N.v49893.
  rewrite ?node_49886.
  rewrite ?node_49887.
  rewrite ?node_49888.
  rewrite ?node_49892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49894 (s : N.State) (i : N.Inputs) :
  R.v49894 (state s) (inputs i) = Zmod.unsigned (N.v49894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49894 s i)) at 1.
  unfold R.v49894, N.v49894.
  unfold R.v6, N.v6.
  rewrite ?node_49893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49895 (s : N.State) (i : N.Inputs) :
  R.v49895 (state s) (inputs i) = Zmod.unsigned (N.v49895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49895 s i)) at 1.
  unfold R.v49895, N.v49895.
  rewrite ?node_7791.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49896 (s : N.State) (i : N.Inputs) :
  R.v49896 (state s) (inputs i) = Zmod.unsigned (N.v49896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49896 s i)) at 1.
  unfold R.v49896, N.v49896.
  unfold R.v6, N.v6.
  rewrite ?node_7903.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49897 (s : N.State) (i : N.Inputs) :
  R.v49897 (state s) (inputs i) = Zmod.unsigned (N.v49897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49897 s i)) at 1.
  unfold R.v49897, N.v49897.
  unfold R.v6, N.v6.
  rewrite ?node_7919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49898 (s : N.State) (i : N.Inputs) :
  R.v49898 (state s) (inputs i) = Zmod.unsigned (N.v49898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49898 s i)) at 1.
  unfold R.v49898, N.v49898.
  rewrite ?node_49895.
  rewrite ?node_49896.
  rewrite ?node_49897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49899 (s : N.State) (i : N.Inputs) :
  R.v49899 (state s) (inputs i) = Zmod.unsigned (N.v49899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49899 s i)) at 1.
  unfold R.v49899, N.v49899.
  rewrite ?node_49894.
  rewrite ?node_49898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49900 (s : N.State) (i : N.Inputs) :
  R.v49900 (state s) (inputs i) = Zmod.unsigned (N.v49900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49900 s i)) at 1.
  unfold R.v49900, N.v49900.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49901 (s : N.State) (i : N.Inputs) :
  R.v49901 (state s) (inputs i) = Zmod.unsigned (N.v49901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49901 s i)) at 1.
  unfold R.v49901, N.v49901.
  rewrite ?node_7782.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49902 (s : N.State) (i : N.Inputs) :
  R.v49902 (state s) (inputs i) = Zmod.unsigned (N.v49902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49902 s i)) at 1.
  unfold R.v49902, N.v49902.
  unfold R.v6, N.v6.
  rewrite ?node_7764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49903 (s : N.State) (i : N.Inputs) :
  R.v49903 (state s) (inputs i) = Zmod.unsigned (N.v49903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49903 s i)) at 1.
  unfold R.v49903, N.v49903.
  unfold R.v6, N.v6.
  rewrite ?node_7737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49904 (s : N.State) (i : N.Inputs) :
  R.v49904 (state s) (inputs i) = Zmod.unsigned (N.v49904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49904 s i)) at 1.
  unfold R.v49904, N.v49904.
  rewrite ?node_49902.
  rewrite ?node_49903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49905 (s : N.State) (i : N.Inputs) :
  R.v49905 (state s) (inputs i) = Zmod.unsigned (N.v49905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49905 s i)) at 1.
  unfold R.v49905, N.v49905.
  unfold R.v16484, N.v16484.
  rewrite ?node_49904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49906 (s : N.State) (i : N.Inputs) :
  R.v49906 (state s) (inputs i) = Zmod.unsigned (N.v49906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49906 s i)) at 1.
  unfold R.v49906, N.v49906.
  rewrite ?node_49901.
  rewrite ?node_49905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49907 (s : N.State) (i : N.Inputs) :
  R.v49907 (state s) (inputs i) = Zmod.unsigned (N.v49907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49907 s i)) at 1.
  unfold R.v49907, N.v49907.
  unfold R.v6, N.v6.
  rewrite ?node_49906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49908 (s : N.State) (i : N.Inputs) :
  R.v49908 (state s) (inputs i) = Zmod.unsigned (N.v49908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49908 s i)) at 1.
  unfold R.v49908, N.v49908.
  rewrite ?node_7783.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49909 (s : N.State) (i : N.Inputs) :
  R.v49909 (state s) (inputs i) = Zmod.unsigned (N.v49909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49909 s i)) at 1.
  unfold R.v49909, N.v49909.
  unfold R.v6, N.v6.
  rewrite ?node_7903.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49910 (s : N.State) (i : N.Inputs) :
  R.v49910 (state s) (inputs i) = Zmod.unsigned (N.v49910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49910 s i)) at 1.
  unfold R.v49910, N.v49910.
  rewrite ?node_49908.
  rewrite ?node_49909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49911 (s : N.State) (i : N.Inputs) :
  R.v49911 (state s) (inputs i) = Zmod.unsigned (N.v49911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49911 s i)) at 1.
  unfold R.v49911, N.v49911.
  rewrite ?node_49907.
  rewrite ?node_49910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49912 (s : N.State) (i : N.Inputs) :
  R.v49912 (state s) (inputs i) = Zmod.unsigned (N.v49912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49912 s i)) at 1.
  unfold R.v49912, N.v49912.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49913 (s : N.State) (i : N.Inputs) :
  R.v49913 (state s) (inputs i) = Zmod.unsigned (N.v49913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49913 s i)) at 1.
  unfold R.v49913, N.v49913.
  rewrite ?node_7790.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49914 (s : N.State) (i : N.Inputs) :
  R.v49914 (state s) (inputs i) = Zmod.unsigned (N.v49914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49914 s i)) at 1.
  unfold R.v49914, N.v49914.
  unfold R.v6, N.v6.
  rewrite ?node_7786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49915 (s : N.State) (i : N.Inputs) :
  R.v49915 (state s) (inputs i) = Zmod.unsigned (N.v49915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49915 s i)) at 1.
  unfold R.v49915, N.v49915.
  unfold R.v6, N.v6.
  rewrite ?node_7783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49916 (s : N.State) (i : N.Inputs) :
  R.v49916 (state s) (inputs i) = Zmod.unsigned (N.v49916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49916 s i)) at 1.
  unfold R.v49916, N.v49916.
  rewrite ?node_49914.
  rewrite ?node_49915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49917 (s : N.State) (i : N.Inputs) :
  R.v49917 (state s) (inputs i) = Zmod.unsigned (N.v49917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49917 s i)) at 1.
  unfold R.v49917, N.v49917.
  unfold R.v16484, N.v16484.
  rewrite ?node_49916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49918 (s : N.State) (i : N.Inputs) :
  R.v49918 (state s) (inputs i) = Zmod.unsigned (N.v49918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49918 s i)) at 1.
  unfold R.v49918, N.v49918.
  rewrite ?node_49913.
  rewrite ?node_49917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49919 (s : N.State) (i : N.Inputs) :
  R.v49919 (state s) (inputs i) = Zmod.unsigned (N.v49919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49919 s i)) at 1.
  unfold R.v49919, N.v49919.
  unfold R.v6, N.v6.
  rewrite ?node_49918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49920 (s : N.State) (i : N.Inputs) :
  R.v49920 (state s) (inputs i) = Zmod.unsigned (N.v49920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49920 s i)) at 1.
  unfold R.v49920, N.v49920.
  rewrite ?node_7791.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49921 (s : N.State) (i : N.Inputs) :
  R.v49921 (state s) (inputs i) = Zmod.unsigned (N.v49921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49921 s i)) at 1.
  unfold R.v49921, N.v49921.
  unfold R.v6, N.v6.
  rewrite ?node_7919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49922 (s : N.State) (i : N.Inputs) :
  R.v49922 (state s) (inputs i) = Zmod.unsigned (N.v49922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49922 s i)) at 1.
  unfold R.v49922, N.v49922.
  rewrite ?node_49920.
  rewrite ?node_49921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49923 (s : N.State) (i : N.Inputs) :
  R.v49923 (state s) (inputs i) = Zmod.unsigned (N.v49923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49923 s i)) at 1.
  unfold R.v49923, N.v49923.
  rewrite ?node_49919.
  rewrite ?node_49922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49924 (s : N.State) (i : N.Inputs) :
  R.v49924 (state s) (inputs i) = Zmod.unsigned (N.v49924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49924 s i)) at 1.
  unfold R.v49924, N.v49924.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49925 (s : N.State) (i : N.Inputs) :
  R.v49925 (state s) (inputs i) = Zmod.unsigned (N.v49925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49925 s i)) at 1.
  unfold R.v49925, N.v49925.
  unfold R.v6, N.v6.
  rewrite ?node_7797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49926 (s : N.State) (i : N.Inputs) :
  R.v49926 (state s) (inputs i) = Zmod.unsigned (N.v49926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49926 s i)) at 1.
  unfold R.v49926, N.v49926.
  unfold R.v6, N.v6.
  rewrite ?node_7794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49927 (s : N.State) (i : N.Inputs) :
  R.v49927 (state s) (inputs i) = Zmod.unsigned (N.v49927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49927 s i)) at 1.
  unfold R.v49927, N.v49927.
  rewrite ?node_49925.
  rewrite ?node_49926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49928 (s : N.State) (i : N.Inputs) :
  R.v49928 (state s) (inputs i) = Zmod.unsigned (N.v49928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49928 s i)) at 1.
  unfold R.v49928, N.v49928.
  unfold R.v16463, N.v16463.
  rewrite ?node_49927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49929 (s : N.State) (i : N.Inputs) :
  R.v49929 (state s) (inputs i) = Zmod.unsigned (N.v49929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49929 s i)) at 1.
  unfold R.v49929, N.v49929.
  rewrite ?node_7798.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49930 (s : N.State) (i : N.Inputs) :
  R.v49930 (state s) (inputs i) = Zmod.unsigned (N.v49930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49930 s i)) at 1.
  unfold R.v49930, N.v49930.
  unfold R.v6, N.v6.
  rewrite ?node_7921.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49931 (s : N.State) (i : N.Inputs) :
  R.v49931 (state s) (inputs i) = Zmod.unsigned (N.v49931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49931 s i)) at 1.
  unfold R.v49931, N.v49931.
  rewrite ?node_49929.
  rewrite ?node_49930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49932 (s : N.State) (i : N.Inputs) :
  R.v49932 (state s) (inputs i) = Zmod.unsigned (N.v49932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49932 s i)) at 1.
  unfold R.v49932, N.v49932.
  rewrite ?node_49928.
  rewrite ?node_49931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49933 (s : N.State) (i : N.Inputs) :
  R.v49933 (state s) (inputs i) = Zmod.unsigned (N.v49933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49933 s i)) at 1.
  unfold R.v49933, N.v49933.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49934 (s : N.State) (i : N.Inputs) :
  R.v49934 (state s) (inputs i) = Zmod.unsigned (N.v49934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49934 s i)) at 1.
  unfold R.v49934, N.v49934.
  rewrite ?node_7903.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49935 (s : N.State) (i : N.Inputs) :
  R.v49935 (state s) (inputs i) = Zmod.unsigned (N.v49935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49935 s i)) at 1.
  unfold R.v49935, N.v49935.
  rewrite ?node_7899.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49936 (s : N.State) (i : N.Inputs) :
  R.v49936 (state s) (inputs i) = Zmod.unsigned (N.v49936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49936 s i)) at 1.
  unfold R.v49936, N.v49936.
  rewrite ?node_7895.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49937 (s : N.State) (i : N.Inputs) :
  R.v49937 (state s) (inputs i) = Zmod.unsigned (N.v49937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49937 s i)) at 1.
  unfold R.v49937, N.v49937.
  unfold R.v6, N.v6.
  rewrite ?node_7875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49938 (s : N.State) (i : N.Inputs) :
  R.v49938 (state s) (inputs i) = Zmod.unsigned (N.v49938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49938 s i)) at 1.
  unfold R.v49938, N.v49938.
  unfold R.v6, N.v6.
  rewrite ?node_7851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49939 (s : N.State) (i : N.Inputs) :
  R.v49939 (state s) (inputs i) = Zmod.unsigned (N.v49939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49939 s i)) at 1.
  unfold R.v49939, N.v49939.
  rewrite ?node_49937.
  rewrite ?node_49938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49940 (s : N.State) (i : N.Inputs) :
  R.v49940 (state s) (inputs i) = Zmod.unsigned (N.v49940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49940 s i)) at 1.
  unfold R.v49940, N.v49940.
  unfold R.v16484, N.v16484.
  rewrite ?node_49939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49941 (s : N.State) (i : N.Inputs) :
  R.v49941 (state s) (inputs i) = Zmod.unsigned (N.v49941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49941 s i)) at 1.
  unfold R.v49941, N.v49941.
  rewrite ?node_49934.
  rewrite ?node_49935.
  rewrite ?node_49936.
  rewrite ?node_49940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49942 (s : N.State) (i : N.Inputs) :
  R.v49942 (state s) (inputs i) = Zmod.unsigned (N.v49942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49942 s i)) at 1.
  unfold R.v49942, N.v49942.
  unfold R.v6, N.v6.
  rewrite ?node_49941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49943 (s : N.State) (i : N.Inputs) :
  R.v49943 (state s) (inputs i) = Zmod.unsigned (N.v49943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49943 s i)) at 1.
  unfold R.v49943, N.v49943.
  rewrite ?node_7904.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49944 (s : N.State) (i : N.Inputs) :
  R.v49944 (state s) (inputs i) = Zmod.unsigned (N.v49944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49944 s i)) at 1.
  unfold R.v49944, N.v49944.
  unfold R.v6, N.v6.
  rewrite ?node_8020.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49945 (s : N.State) (i : N.Inputs) :
  R.v49945 (state s) (inputs i) = Zmod.unsigned (N.v49945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49945 s i)) at 1.
  unfold R.v49945, N.v49945.
  unfold R.v6, N.v6.
  rewrite ?node_8036.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49946 (s : N.State) (i : N.Inputs) :
  R.v49946 (state s) (inputs i) = Zmod.unsigned (N.v49946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49946 s i)) at 1.
  unfold R.v49946, N.v49946.
  rewrite ?node_49943.
  rewrite ?node_49944.
  rewrite ?node_49945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49947 (s : N.State) (i : N.Inputs) :
  R.v49947 (state s) (inputs i) = Zmod.unsigned (N.v49947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49947 s i)) at 1.
  unfold R.v49947, N.v49947.
  rewrite ?node_49942.
  rewrite ?node_49946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49948 (s : N.State) (i : N.Inputs) :
  R.v49948 (state s) (inputs i) = Zmod.unsigned (N.v49948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49948 s i)) at 1.
  unfold R.v49948, N.v49948.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49949 (s : N.State) (i : N.Inputs) :
  R.v49949 (state s) (inputs i) = Zmod.unsigned (N.v49949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49949 s i)) at 1.
  unfold R.v49949, N.v49949.
  rewrite ?node_7895.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49950 (s : N.State) (i : N.Inputs) :
  R.v49950 (state s) (inputs i) = Zmod.unsigned (N.v49950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49950 s i)) at 1.
  unfold R.v49950, N.v49950.
  unfold R.v6, N.v6.
  rewrite ?node_7875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49951 (s : N.State) (i : N.Inputs) :
  R.v49951 (state s) (inputs i) = Zmod.unsigned (N.v49951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49951 s i)) at 1.
  unfold R.v49951, N.v49951.
  unfold R.v6, N.v6.
  rewrite ?node_7851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49952 (s : N.State) (i : N.Inputs) :
  R.v49952 (state s) (inputs i) = Zmod.unsigned (N.v49952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49952 s i)) at 1.
  unfold R.v49952, N.v49952.
  rewrite ?node_49950.
  rewrite ?node_49951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49953 (s : N.State) (i : N.Inputs) :
  R.v49953 (state s) (inputs i) = Zmod.unsigned (N.v49953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49953 s i)) at 1.
  unfold R.v49953, N.v49953.
  unfold R.v16484, N.v16484.
  rewrite ?node_49952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49954 (s : N.State) (i : N.Inputs) :
  R.v49954 (state s) (inputs i) = Zmod.unsigned (N.v49954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49954 s i)) at 1.
  unfold R.v49954, N.v49954.
  rewrite ?node_49949.
  rewrite ?node_49953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49955 (s : N.State) (i : N.Inputs) :
  R.v49955 (state s) (inputs i) = Zmod.unsigned (N.v49955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49955 s i)) at 1.
  unfold R.v49955, N.v49955.
  unfold R.v6, N.v6.
  rewrite ?node_49954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49956 (s : N.State) (i : N.Inputs) :
  R.v49956 (state s) (inputs i) = Zmod.unsigned (N.v49956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49956 s i)) at 1.
  unfold R.v49956, N.v49956.
  rewrite ?node_7896.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49957 (s : N.State) (i : N.Inputs) :
  R.v49957 (state s) (inputs i) = Zmod.unsigned (N.v49957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49957 s i)) at 1.
  unfold R.v49957, N.v49957.
  unfold R.v6, N.v6.
  rewrite ?node_8020.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49958 (s : N.State) (i : N.Inputs) :
  R.v49958 (state s) (inputs i) = Zmod.unsigned (N.v49958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49958 s i)) at 1.
  unfold R.v49958, N.v49958.
  rewrite ?node_49956.
  rewrite ?node_49957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49959 (s : N.State) (i : N.Inputs) :
  R.v49959 (state s) (inputs i) = Zmod.unsigned (N.v49959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49959 s i)) at 1.
  unfold R.v49959, N.v49959.
  rewrite ?node_49955.
  rewrite ?node_49958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49960 (s : N.State) (i : N.Inputs) :
  R.v49960 (state s) (inputs i) = Zmod.unsigned (N.v49960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49960 s i)) at 1.
  unfold R.v49960, N.v49960.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49961 (s : N.State) (i : N.Inputs) :
  R.v49961 (state s) (inputs i) = Zmod.unsigned (N.v49961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49961 s i)) at 1.
  unfold R.v49961, N.v49961.
  rewrite ?node_7903.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49962 (s : N.State) (i : N.Inputs) :
  R.v49962 (state s) (inputs i) = Zmod.unsigned (N.v49962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49962 s i)) at 1.
  unfold R.v49962, N.v49962.
  unfold R.v6, N.v6.
  rewrite ?node_7899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49963 (s : N.State) (i : N.Inputs) :
  R.v49963 (state s) (inputs i) = Zmod.unsigned (N.v49963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49963 s i)) at 1.
  unfold R.v49963, N.v49963.
  unfold R.v6, N.v6.
  rewrite ?node_7896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49964 (s : N.State) (i : N.Inputs) :
  R.v49964 (state s) (inputs i) = Zmod.unsigned (N.v49964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49964 s i)) at 1.
  unfold R.v49964, N.v49964.
  rewrite ?node_49962.
  rewrite ?node_49963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49965 (s : N.State) (i : N.Inputs) :
  R.v49965 (state s) (inputs i) = Zmod.unsigned (N.v49965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49965 s i)) at 1.
  unfold R.v49965, N.v49965.
  unfold R.v16484, N.v16484.
  rewrite ?node_49964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49966 (s : N.State) (i : N.Inputs) :
  R.v49966 (state s) (inputs i) = Zmod.unsigned (N.v49966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49966 s i)) at 1.
  unfold R.v49966, N.v49966.
  rewrite ?node_49961.
  rewrite ?node_49965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49967 (s : N.State) (i : N.Inputs) :
  R.v49967 (state s) (inputs i) = Zmod.unsigned (N.v49967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49967 s i)) at 1.
  unfold R.v49967, N.v49967.
  unfold R.v6, N.v6.
  rewrite ?node_49966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49968 (s : N.State) (i : N.Inputs) :
  R.v49968 (state s) (inputs i) = Zmod.unsigned (N.v49968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49968 s i)) at 1.
  unfold R.v49968, N.v49968.
  rewrite ?node_7904.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49969 (s : N.State) (i : N.Inputs) :
  R.v49969 (state s) (inputs i) = Zmod.unsigned (N.v49969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49969 s i)) at 1.
  unfold R.v49969, N.v49969.
  unfold R.v6, N.v6.
  rewrite ?node_8036.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49970 (s : N.State) (i : N.Inputs) :
  R.v49970 (state s) (inputs i) = Zmod.unsigned (N.v49970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49970 s i)) at 1.
  unfold R.v49970, N.v49970.
  rewrite ?node_49968.
  rewrite ?node_49969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49971 (s : N.State) (i : N.Inputs) :
  R.v49971 (state s) (inputs i) = Zmod.unsigned (N.v49971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49971 s i)) at 1.
  unfold R.v49971, N.v49971.
  rewrite ?node_49967.
  rewrite ?node_49970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49972 (s : N.State) (i : N.Inputs) :
  R.v49972 (state s) (inputs i) = Zmod.unsigned (N.v49972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49972 s i)) at 1.
  unfold R.v49972, N.v49972.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49973 (s : N.State) (i : N.Inputs) :
  R.v49973 (state s) (inputs i) = Zmod.unsigned (N.v49973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49973 s i)) at 1.
  unfold R.v49973, N.v49973.
  rewrite ?node_7914.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49974 (s : N.State) (i : N.Inputs) :
  R.v49974 (state s) (inputs i) = Zmod.unsigned (N.v49974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49974 s i)) at 1.
  unfold R.v49974, N.v49974.
  unfold R.v6, N.v6.
  rewrite ?node_7910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49975 (s : N.State) (i : N.Inputs) :
  R.v49975 (state s) (inputs i) = Zmod.unsigned (N.v49975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49975 s i)) at 1.
  unfold R.v49975, N.v49975.
  unfold R.v6, N.v6.
  rewrite ?node_7907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49976 (s : N.State) (i : N.Inputs) :
  R.v49976 (state s) (inputs i) = Zmod.unsigned (N.v49976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49976 s i)) at 1.
  unfold R.v49976, N.v49976.
  rewrite ?node_49974.
  rewrite ?node_49975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49977 (s : N.State) (i : N.Inputs) :
  R.v49977 (state s) (inputs i) = Zmod.unsigned (N.v49977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49977 s i)) at 1.
  unfold R.v49977, N.v49977.
  unfold R.v16484, N.v16484.
  rewrite ?node_49976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49978 (s : N.State) (i : N.Inputs) :
  R.v49978 (state s) (inputs i) = Zmod.unsigned (N.v49978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49978 s i)) at 1.
  unfold R.v49978, N.v49978.
  rewrite ?node_49973.
  rewrite ?node_49977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49979 (s : N.State) (i : N.Inputs) :
  R.v49979 (state s) (inputs i) = Zmod.unsigned (N.v49979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49979 s i)) at 1.
  unfold R.v49979, N.v49979.
  unfold R.v6, N.v6.
  rewrite ?node_49978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49980 (s : N.State) (i : N.Inputs) :
  R.v49980 (state s) (inputs i) = Zmod.unsigned (N.v49980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49980 s i)) at 1.
  unfold R.v49980, N.v49980.
  rewrite ?node_7915.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49981 (s : N.State) (i : N.Inputs) :
  R.v49981 (state s) (inputs i) = Zmod.unsigned (N.v49981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49981 s i)) at 1.
  unfold R.v49981, N.v49981.
  unfold R.v6, N.v6.
  rewrite ?node_8040.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49982 (s : N.State) (i : N.Inputs) :
  R.v49982 (state s) (inputs i) = Zmod.unsigned (N.v49982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49982 s i)) at 1.
  unfold R.v49982, N.v49982.
  rewrite ?node_49980.
  rewrite ?node_49981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49983 (s : N.State) (i : N.Inputs) :
  R.v49983 (state s) (inputs i) = Zmod.unsigned (N.v49983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49983 s i)) at 1.
  unfold R.v49983, N.v49983.
  rewrite ?node_49979.
  rewrite ?node_49982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49984 (s : N.State) (i : N.Inputs) :
  R.v49984 (state s) (inputs i) = Zmod.unsigned (N.v49984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49984 s i)) at 1.
  unfold R.v49984, N.v49984.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49985 (s : N.State) (i : N.Inputs) :
  R.v49985 (state s) (inputs i) = Zmod.unsigned (N.v49985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49985 s i)) at 1.
  unfold R.v49985, N.v49985.
  rewrite ?node_8020.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49986 (s : N.State) (i : N.Inputs) :
  R.v49986 (state s) (inputs i) = Zmod.unsigned (N.v49986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49986 s i)) at 1.
  unfold R.v49986, N.v49986.
  rewrite ?node_8016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49987 (s : N.State) (i : N.Inputs) :
  R.v49987 (state s) (inputs i) = Zmod.unsigned (N.v49987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49987 s i)) at 1.
  unfold R.v49987, N.v49987.
  rewrite ?node_8012.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49988 (s : N.State) (i : N.Inputs) :
  R.v49988 (state s) (inputs i) = Zmod.unsigned (N.v49988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49988 s i)) at 1.
  unfold R.v49988, N.v49988.
  unfold R.v6, N.v6.
  rewrite ?node_7992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49989 (s : N.State) (i : N.Inputs) :
  R.v49989 (state s) (inputs i) = Zmod.unsigned (N.v49989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49989 s i)) at 1.
  unfold R.v49989, N.v49989.
  unfold R.v6, N.v6.
  rewrite ?node_7968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49990 (s : N.State) (i : N.Inputs) :
  R.v49990 (state s) (inputs i) = Zmod.unsigned (N.v49990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49990 s i)) at 1.
  unfold R.v49990, N.v49990.
  rewrite ?node_49988.
  rewrite ?node_49989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49991 (s : N.State) (i : N.Inputs) :
  R.v49991 (state s) (inputs i) = Zmod.unsigned (N.v49991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49991 s i)) at 1.
  unfold R.v49991, N.v49991.
  unfold R.v16484, N.v16484.
  rewrite ?node_49990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49992 (s : N.State) (i : N.Inputs) :
  R.v49992 (state s) (inputs i) = Zmod.unsigned (N.v49992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49992 s i)) at 1.
  unfold R.v49992, N.v49992.
  rewrite ?node_49985.
  rewrite ?node_49986.
  rewrite ?node_49987.
  rewrite ?node_49991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49993 (s : N.State) (i : N.Inputs) :
  R.v49993 (state s) (inputs i) = Zmod.unsigned (N.v49993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49993 s i)) at 1.
  unfold R.v49993, N.v49993.
  unfold R.v6, N.v6.
  rewrite ?node_49992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49994 (s : N.State) (i : N.Inputs) :
  R.v49994 (state s) (inputs i) = Zmod.unsigned (N.v49994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49994 s i)) at 1.
  unfold R.v49994, N.v49994.
  rewrite ?node_8021.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49995 (s : N.State) (i : N.Inputs) :
  R.v49995 (state s) (inputs i) = Zmod.unsigned (N.v49995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49995 s i)) at 1.
  unfold R.v49995, N.v49995.
  unfold R.v6, N.v6.
  rewrite ?node_8140.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49996 (s : N.State) (i : N.Inputs) :
  R.v49996 (state s) (inputs i) = Zmod.unsigned (N.v49996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49996 s i)) at 1.
  unfold R.v49996, N.v49996.
  unfold R.v6, N.v6.
  rewrite ?node_8156.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49997 (s : N.State) (i : N.Inputs) :
  R.v49997 (state s) (inputs i) = Zmod.unsigned (N.v49997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49997 s i)) at 1.
  unfold R.v49997, N.v49997.
  rewrite ?node_49994.
  rewrite ?node_49995.
  rewrite ?node_49996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49998 (s : N.State) (i : N.Inputs) :
  R.v49998 (state s) (inputs i) = Zmod.unsigned (N.v49998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49998 s i)) at 1.
  unfold R.v49998, N.v49998.
  rewrite ?node_49993.
  rewrite ?node_49997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49999 (s : N.State) (i : N.Inputs) :
  R.v49999 (state s) (inputs i) = Zmod.unsigned (N.v49999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49999 s i)) at 1.
  unfold R.v49999, N.v49999.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
