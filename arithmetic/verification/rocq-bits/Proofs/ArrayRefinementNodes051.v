(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes050.
Lemma node_51000 (s : N.State) (i : N.Inputs) :
  R.v51000 (state s) (inputs i) = Zmod.unsigned (N.v51000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51000 s i)) at 1.
  unfold R.v51000, N.v51000.
  unfold R.v6, N.v6.
  rewrite ?node_50999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51001 (s : N.State) (i : N.Inputs) :
  R.v51001 (state s) (inputs i) = Zmod.unsigned (N.v51001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51001 s i)) at 1.
  unfold R.v51001, N.v51001.
  rewrite ?node_9929.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51002 (s : N.State) (i : N.Inputs) :
  R.v51002 (state s) (inputs i) = Zmod.unsigned (N.v51002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51002 s i)) at 1.
  unfold R.v51002, N.v51002.
  unfold R.v6, N.v6.
  rewrite ?node_10079.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51003 (s : N.State) (i : N.Inputs) :
  R.v51003 (state s) (inputs i) = Zmod.unsigned (N.v51003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51003 s i)) at 1.
  unfold R.v51003, N.v51003.
  unfold R.v6, N.v6.
  rewrite ?node_10107.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51004 (s : N.State) (i : N.Inputs) :
  R.v51004 (state s) (inputs i) = Zmod.unsigned (N.v51004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51004 s i)) at 1.
  unfold R.v51004, N.v51004.
  rewrite ?node_51001.
  rewrite ?node_51002.
  rewrite ?node_51003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51005 (s : N.State) (i : N.Inputs) :
  R.v51005 (state s) (inputs i) = Zmod.unsigned (N.v51005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51005 s i)) at 1.
  unfold R.v51005, N.v51005.
  rewrite ?node_51000.
  rewrite ?node_51004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51006 (s : N.State) (i : N.Inputs) :
  R.v51006 (state s) (inputs i) = Zmod.unsigned (N.v51006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51006 s i)) at 1.
  unfold R.v51006, N.v51006.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51007 (s : N.State) (i : N.Inputs) :
  R.v51007 (state s) (inputs i) = Zmod.unsigned (N.v51007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51007 s i)) at 1.
  unfold R.v51007, N.v51007.
  rewrite ?node_9906.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51008 (s : N.State) (i : N.Inputs) :
  R.v51008 (state s) (inputs i) = Zmod.unsigned (N.v51008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51008 s i)) at 1.
  unfold R.v51008, N.v51008.
  unfold R.v6, N.v6.
  rewrite ?node_9886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51009 (s : N.State) (i : N.Inputs) :
  R.v51009 (state s) (inputs i) = Zmod.unsigned (N.v51009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51009 s i)) at 1.
  unfold R.v51009, N.v51009.
  unfold R.v6, N.v6.
  rewrite ?node_9851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51010 (s : N.State) (i : N.Inputs) :
  R.v51010 (state s) (inputs i) = Zmod.unsigned (N.v51010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51010 s i)) at 1.
  unfold R.v51010, N.v51010.
  rewrite ?node_51008.
  rewrite ?node_51009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51011 (s : N.State) (i : N.Inputs) :
  R.v51011 (state s) (inputs i) = Zmod.unsigned (N.v51011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51011 s i)) at 1.
  unfold R.v51011, N.v51011.
  unfold R.v16484, N.v16484.
  rewrite ?node_51010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51012 (s : N.State) (i : N.Inputs) :
  R.v51012 (state s) (inputs i) = Zmod.unsigned (N.v51012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51012 s i)) at 1.
  unfold R.v51012, N.v51012.
  rewrite ?node_51007.
  rewrite ?node_51011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51013 (s : N.State) (i : N.Inputs) :
  R.v51013 (state s) (inputs i) = Zmod.unsigned (N.v51013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51013 s i)) at 1.
  unfold R.v51013, N.v51013.
  unfold R.v6, N.v6.
  rewrite ?node_51012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51014 (s : N.State) (i : N.Inputs) :
  R.v51014 (state s) (inputs i) = Zmod.unsigned (N.v51014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51014 s i)) at 1.
  unfold R.v51014, N.v51014.
  rewrite ?node_9907.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51015 (s : N.State) (i : N.Inputs) :
  R.v51015 (state s) (inputs i) = Zmod.unsigned (N.v51015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51015 s i)) at 1.
  unfold R.v51015, N.v51015.
  unfold R.v6, N.v6.
  rewrite ?node_10079.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51016 (s : N.State) (i : N.Inputs) :
  R.v51016 (state s) (inputs i) = Zmod.unsigned (N.v51016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51016 s i)) at 1.
  unfold R.v51016, N.v51016.
  rewrite ?node_51014.
  rewrite ?node_51015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51017 (s : N.State) (i : N.Inputs) :
  R.v51017 (state s) (inputs i) = Zmod.unsigned (N.v51017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51017 s i)) at 1.
  unfold R.v51017, N.v51017.
  rewrite ?node_51013.
  rewrite ?node_51016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51018 (s : N.State) (i : N.Inputs) :
  R.v51018 (state s) (inputs i) = Zmod.unsigned (N.v51018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51018 s i)) at 1.
  unfold R.v51018, N.v51018.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51019 (s : N.State) (i : N.Inputs) :
  R.v51019 (state s) (inputs i) = Zmod.unsigned (N.v51019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51019 s i)) at 1.
  unfold R.v51019, N.v51019.
  rewrite ?node_9928.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51020 (s : N.State) (i : N.Inputs) :
  R.v51020 (state s) (inputs i) = Zmod.unsigned (N.v51020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51020 s i)) at 1.
  unfold R.v51020, N.v51020.
  unfold R.v6, N.v6.
  rewrite ?node_9924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51021 (s : N.State) (i : N.Inputs) :
  R.v51021 (state s) (inputs i) = Zmod.unsigned (N.v51021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51021 s i)) at 1.
  unfold R.v51021, N.v51021.
  unfold R.v6, N.v6.
  rewrite ?node_9907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51022 (s : N.State) (i : N.Inputs) :
  R.v51022 (state s) (inputs i) = Zmod.unsigned (N.v51022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51022 s i)) at 1.
  unfold R.v51022, N.v51022.
  rewrite ?node_51020.
  rewrite ?node_51021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51023 (s : N.State) (i : N.Inputs) :
  R.v51023 (state s) (inputs i) = Zmod.unsigned (N.v51023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51023 s i)) at 1.
  unfold R.v51023, N.v51023.
  unfold R.v16484, N.v16484.
  rewrite ?node_51022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51024 (s : N.State) (i : N.Inputs) :
  R.v51024 (state s) (inputs i) = Zmod.unsigned (N.v51024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51024 s i)) at 1.
  unfold R.v51024, N.v51024.
  rewrite ?node_51019.
  rewrite ?node_51023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51025 (s : N.State) (i : N.Inputs) :
  R.v51025 (state s) (inputs i) = Zmod.unsigned (N.v51025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51025 s i)) at 1.
  unfold R.v51025, N.v51025.
  unfold R.v6, N.v6.
  rewrite ?node_51024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51026 (s : N.State) (i : N.Inputs) :
  R.v51026 (state s) (inputs i) = Zmod.unsigned (N.v51026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51026 s i)) at 1.
  unfold R.v51026, N.v51026.
  rewrite ?node_9929.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51027 (s : N.State) (i : N.Inputs) :
  R.v51027 (state s) (inputs i) = Zmod.unsigned (N.v51027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51027 s i)) at 1.
  unfold R.v51027, N.v51027.
  unfold R.v6, N.v6.
  rewrite ?node_10107.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51028 (s : N.State) (i : N.Inputs) :
  R.v51028 (state s) (inputs i) = Zmod.unsigned (N.v51028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51028 s i)) at 1.
  unfold R.v51028, N.v51028.
  rewrite ?node_51026.
  rewrite ?node_51027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51029 (s : N.State) (i : N.Inputs) :
  R.v51029 (state s) (inputs i) = Zmod.unsigned (N.v51029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51029 s i)) at 1.
  unfold R.v51029, N.v51029.
  rewrite ?node_51025.
  rewrite ?node_51028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51030 (s : N.State) (i : N.Inputs) :
  R.v51030 (state s) (inputs i) = Zmod.unsigned (N.v51030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51030 s i)) at 1.
  unfold R.v51030, N.v51030.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51031 (s : N.State) (i : N.Inputs) :
  R.v51031 (state s) (inputs i) = Zmod.unsigned (N.v51031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51031 s i)) at 1.
  unfold R.v51031, N.v51031.
  rewrite ?node_9947.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51032 (s : N.State) (i : N.Inputs) :
  R.v51032 (state s) (inputs i) = Zmod.unsigned (N.v51032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51032 s i)) at 1.
  unfold R.v51032, N.v51032.
  rewrite ?node_9943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51033 (s : N.State) (i : N.Inputs) :
  R.v51033 (state s) (inputs i) = Zmod.unsigned (N.v51033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51033 s i)) at 1.
  unfold R.v51033, N.v51033.
  rewrite ?node_9939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51034 (s : N.State) (i : N.Inputs) :
  R.v51034 (state s) (inputs i) = Zmod.unsigned (N.v51034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51034 s i)) at 1.
  unfold R.v51034, N.v51034.
  unfold R.v6, N.v6.
  rewrite ?node_9935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51035 (s : N.State) (i : N.Inputs) :
  R.v51035 (state s) (inputs i) = Zmod.unsigned (N.v51035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51035 s i)) at 1.
  unfold R.v51035, N.v51035.
  unfold R.v6, N.v6.
  rewrite ?node_9932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51036 (s : N.State) (i : N.Inputs) :
  R.v51036 (state s) (inputs i) = Zmod.unsigned (N.v51036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51036 s i)) at 1.
  unfold R.v51036, N.v51036.
  rewrite ?node_51034.
  rewrite ?node_51035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51037 (s : N.State) (i : N.Inputs) :
  R.v51037 (state s) (inputs i) = Zmod.unsigned (N.v51037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51037 s i)) at 1.
  unfold R.v51037, N.v51037.
  unfold R.v16484, N.v16484.
  rewrite ?node_51036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51038 (s : N.State) (i : N.Inputs) :
  R.v51038 (state s) (inputs i) = Zmod.unsigned (N.v51038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51038 s i)) at 1.
  unfold R.v51038, N.v51038.
  rewrite ?node_51031.
  rewrite ?node_51032.
  rewrite ?node_51033.
  rewrite ?node_51037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51039 (s : N.State) (i : N.Inputs) :
  R.v51039 (state s) (inputs i) = Zmod.unsigned (N.v51039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51039 s i)) at 1.
  unfold R.v51039, N.v51039.
  unfold R.v6, N.v6.
  rewrite ?node_51038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51040 (s : N.State) (i : N.Inputs) :
  R.v51040 (state s) (inputs i) = Zmod.unsigned (N.v51040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51040 s i)) at 1.
  unfold R.v51040, N.v51040.
  rewrite ?node_9948.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51041 (s : N.State) (i : N.Inputs) :
  R.v51041 (state s) (inputs i) = Zmod.unsigned (N.v51041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51041 s i)) at 1.
  unfold R.v51041, N.v51041.
  unfold R.v6, N.v6.
  rewrite ?node_10098.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51042 (s : N.State) (i : N.Inputs) :
  R.v51042 (state s) (inputs i) = Zmod.unsigned (N.v51042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51042 s i)) at 1.
  unfold R.v51042, N.v51042.
  unfold R.v6, N.v6.
  rewrite ?node_10115.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51043 (s : N.State) (i : N.Inputs) :
  R.v51043 (state s) (inputs i) = Zmod.unsigned (N.v51043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51043 s i)) at 1.
  unfold R.v51043, N.v51043.
  rewrite ?node_51040.
  rewrite ?node_51041.
  rewrite ?node_51042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51044 (s : N.State) (i : N.Inputs) :
  R.v51044 (state s) (inputs i) = Zmod.unsigned (N.v51044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51044 s i)) at 1.
  unfold R.v51044, N.v51044.
  rewrite ?node_51039.
  rewrite ?node_51043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51045 (s : N.State) (i : N.Inputs) :
  R.v51045 (state s) (inputs i) = Zmod.unsigned (N.v51045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51045 s i)) at 1.
  unfold R.v51045, N.v51045.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51046 (s : N.State) (i : N.Inputs) :
  R.v51046 (state s) (inputs i) = Zmod.unsigned (N.v51046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51046 s i)) at 1.
  unfold R.v51046, N.v51046.
  rewrite ?node_9939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51047 (s : N.State) (i : N.Inputs) :
  R.v51047 (state s) (inputs i) = Zmod.unsigned (N.v51047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51047 s i)) at 1.
  unfold R.v51047, N.v51047.
  unfold R.v6, N.v6.
  rewrite ?node_9935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51048 (s : N.State) (i : N.Inputs) :
  R.v51048 (state s) (inputs i) = Zmod.unsigned (N.v51048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51048 s i)) at 1.
  unfold R.v51048, N.v51048.
  unfold R.v6, N.v6.
  rewrite ?node_9932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51049 (s : N.State) (i : N.Inputs) :
  R.v51049 (state s) (inputs i) = Zmod.unsigned (N.v51049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51049 s i)) at 1.
  unfold R.v51049, N.v51049.
  rewrite ?node_51047.
  rewrite ?node_51048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51050 (s : N.State) (i : N.Inputs) :
  R.v51050 (state s) (inputs i) = Zmod.unsigned (N.v51050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51050 s i)) at 1.
  unfold R.v51050, N.v51050.
  unfold R.v16484, N.v16484.
  rewrite ?node_51049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51051 (s : N.State) (i : N.Inputs) :
  R.v51051 (state s) (inputs i) = Zmod.unsigned (N.v51051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51051 s i)) at 1.
  unfold R.v51051, N.v51051.
  rewrite ?node_51046.
  rewrite ?node_51050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51052 (s : N.State) (i : N.Inputs) :
  R.v51052 (state s) (inputs i) = Zmod.unsigned (N.v51052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51052 s i)) at 1.
  unfold R.v51052, N.v51052.
  unfold R.v6, N.v6.
  rewrite ?node_51051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51053 (s : N.State) (i : N.Inputs) :
  R.v51053 (state s) (inputs i) = Zmod.unsigned (N.v51053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51053 s i)) at 1.
  unfold R.v51053, N.v51053.
  rewrite ?node_9940.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51054 (s : N.State) (i : N.Inputs) :
  R.v51054 (state s) (inputs i) = Zmod.unsigned (N.v51054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51054 s i)) at 1.
  unfold R.v51054, N.v51054.
  unfold R.v6, N.v6.
  rewrite ?node_10098.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51055 (s : N.State) (i : N.Inputs) :
  R.v51055 (state s) (inputs i) = Zmod.unsigned (N.v51055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51055 s i)) at 1.
  unfold R.v51055, N.v51055.
  rewrite ?node_51053.
  rewrite ?node_51054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51056 (s : N.State) (i : N.Inputs) :
  R.v51056 (state s) (inputs i) = Zmod.unsigned (N.v51056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51056 s i)) at 1.
  unfold R.v51056, N.v51056.
  rewrite ?node_51052.
  rewrite ?node_51055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51057 (s : N.State) (i : N.Inputs) :
  R.v51057 (state s) (inputs i) = Zmod.unsigned (N.v51057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51057 s i)) at 1.
  unfold R.v51057, N.v51057.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51058 (s : N.State) (i : N.Inputs) :
  R.v51058 (state s) (inputs i) = Zmod.unsigned (N.v51058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51058 s i)) at 1.
  unfold R.v51058, N.v51058.
  rewrite ?node_9947.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51059 (s : N.State) (i : N.Inputs) :
  R.v51059 (state s) (inputs i) = Zmod.unsigned (N.v51059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51059 s i)) at 1.
  unfold R.v51059, N.v51059.
  unfold R.v6, N.v6.
  rewrite ?node_9943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51060 (s : N.State) (i : N.Inputs) :
  R.v51060 (state s) (inputs i) = Zmod.unsigned (N.v51060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51060 s i)) at 1.
  unfold R.v51060, N.v51060.
  unfold R.v6, N.v6.
  rewrite ?node_9940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51061 (s : N.State) (i : N.Inputs) :
  R.v51061 (state s) (inputs i) = Zmod.unsigned (N.v51061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51061 s i)) at 1.
  unfold R.v51061, N.v51061.
  rewrite ?node_51059.
  rewrite ?node_51060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51062 (s : N.State) (i : N.Inputs) :
  R.v51062 (state s) (inputs i) = Zmod.unsigned (N.v51062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51062 s i)) at 1.
  unfold R.v51062, N.v51062.
  unfold R.v16484, N.v16484.
  rewrite ?node_51061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51063 (s : N.State) (i : N.Inputs) :
  R.v51063 (state s) (inputs i) = Zmod.unsigned (N.v51063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51063 s i)) at 1.
  unfold R.v51063, N.v51063.
  rewrite ?node_51058.
  rewrite ?node_51062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51064 (s : N.State) (i : N.Inputs) :
  R.v51064 (state s) (inputs i) = Zmod.unsigned (N.v51064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51064 s i)) at 1.
  unfold R.v51064, N.v51064.
  unfold R.v6, N.v6.
  rewrite ?node_51063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51065 (s : N.State) (i : N.Inputs) :
  R.v51065 (state s) (inputs i) = Zmod.unsigned (N.v51065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51065 s i)) at 1.
  unfold R.v51065, N.v51065.
  rewrite ?node_9948.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51066 (s : N.State) (i : N.Inputs) :
  R.v51066 (state s) (inputs i) = Zmod.unsigned (N.v51066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51066 s i)) at 1.
  unfold R.v51066, N.v51066.
  unfold R.v6, N.v6.
  rewrite ?node_10115.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51067 (s : N.State) (i : N.Inputs) :
  R.v51067 (state s) (inputs i) = Zmod.unsigned (N.v51067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51067 s i)) at 1.
  unfold R.v51067, N.v51067.
  rewrite ?node_51065.
  rewrite ?node_51066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51068 (s : N.State) (i : N.Inputs) :
  R.v51068 (state s) (inputs i) = Zmod.unsigned (N.v51068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51068 s i)) at 1.
  unfold R.v51068, N.v51068.
  rewrite ?node_51064.
  rewrite ?node_51067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51069 (s : N.State) (i : N.Inputs) :
  R.v51069 (state s) (inputs i) = Zmod.unsigned (N.v51069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51069 s i)) at 1.
  unfold R.v51069, N.v51069.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51070 (s : N.State) (i : N.Inputs) :
  R.v51070 (state s) (inputs i) = Zmod.unsigned (N.v51070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51070 s i)) at 1.
  unfold R.v51070, N.v51070.
  rewrite ?node_10079.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51071 (s : N.State) (i : N.Inputs) :
  R.v51071 (state s) (inputs i) = Zmod.unsigned (N.v51071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51071 s i)) at 1.
  unfold R.v51071, N.v51071.
  rewrite ?node_10075.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51072 (s : N.State) (i : N.Inputs) :
  R.v51072 (state s) (inputs i) = Zmod.unsigned (N.v51072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51072 s i)) at 1.
  unfold R.v51072, N.v51072.
  rewrite ?node_10055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51073 (s : N.State) (i : N.Inputs) :
  R.v51073 (state s) (inputs i) = Zmod.unsigned (N.v51073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51073 s i)) at 1.
  unfold R.v51073, N.v51073.
  unfold R.v6, N.v6.
  rewrite ?node_10038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51074 (s : N.State) (i : N.Inputs) :
  R.v51074 (state s) (inputs i) = Zmod.unsigned (N.v51074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51074 s i)) at 1.
  unfold R.v51074, N.v51074.
  unfold R.v6, N.v6.
  rewrite ?node_10003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51075 (s : N.State) (i : N.Inputs) :
  R.v51075 (state s) (inputs i) = Zmod.unsigned (N.v51075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51075 s i)) at 1.
  unfold R.v51075, N.v51075.
  rewrite ?node_51073.
  rewrite ?node_51074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51076 (s : N.State) (i : N.Inputs) :
  R.v51076 (state s) (inputs i) = Zmod.unsigned (N.v51076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51076 s i)) at 1.
  unfold R.v51076, N.v51076.
  unfold R.v16484, N.v16484.
  rewrite ?node_51075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51077 (s : N.State) (i : N.Inputs) :
  R.v51077 (state s) (inputs i) = Zmod.unsigned (N.v51077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51077 s i)) at 1.
  unfold R.v51077, N.v51077.
  rewrite ?node_51070.
  rewrite ?node_51071.
  rewrite ?node_51072.
  rewrite ?node_51076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51078 (s : N.State) (i : N.Inputs) :
  R.v51078 (state s) (inputs i) = Zmod.unsigned (N.v51078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51078 s i)) at 1.
  unfold R.v51078, N.v51078.
  unfold R.v6, N.v6.
  rewrite ?node_51077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51079 (s : N.State) (i : N.Inputs) :
  R.v51079 (state s) (inputs i) = Zmod.unsigned (N.v51079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51079 s i)) at 1.
  unfold R.v51079, N.v51079.
  rewrite ?node_10080.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51080 (s : N.State) (i : N.Inputs) :
  R.v51080 (state s) (inputs i) = Zmod.unsigned (N.v51080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51080 s i)) at 1.
  unfold R.v51080, N.v51080.
  unfold R.v6, N.v6.
  rewrite ?node_10234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51081 (s : N.State) (i : N.Inputs) :
  R.v51081 (state s) (inputs i) = Zmod.unsigned (N.v51081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51081 s i)) at 1.
  unfold R.v51081, N.v51081.
  unfold R.v6, N.v6.
  rewrite ?node_10262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51082 (s : N.State) (i : N.Inputs) :
  R.v51082 (state s) (inputs i) = Zmod.unsigned (N.v51082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51082 s i)) at 1.
  unfold R.v51082, N.v51082.
  rewrite ?node_51079.
  rewrite ?node_51080.
  rewrite ?node_51081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51083 (s : N.State) (i : N.Inputs) :
  R.v51083 (state s) (inputs i) = Zmod.unsigned (N.v51083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51083 s i)) at 1.
  unfold R.v51083, N.v51083.
  rewrite ?node_51078.
  rewrite ?node_51082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51084 (s : N.State) (i : N.Inputs) :
  R.v51084 (state s) (inputs i) = Zmod.unsigned (N.v51084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51084 s i)) at 1.
  unfold R.v51084, N.v51084.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51085 (s : N.State) (i : N.Inputs) :
  R.v51085 (state s) (inputs i) = Zmod.unsigned (N.v51085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51085 s i)) at 1.
  unfold R.v51085, N.v51085.
  rewrite ?node_10055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51086 (s : N.State) (i : N.Inputs) :
  R.v51086 (state s) (inputs i) = Zmod.unsigned (N.v51086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51086 s i)) at 1.
  unfold R.v51086, N.v51086.
  unfold R.v6, N.v6.
  rewrite ?node_10038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51087 (s : N.State) (i : N.Inputs) :
  R.v51087 (state s) (inputs i) = Zmod.unsigned (N.v51087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51087 s i)) at 1.
  unfold R.v51087, N.v51087.
  unfold R.v6, N.v6.
  rewrite ?node_10003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51088 (s : N.State) (i : N.Inputs) :
  R.v51088 (state s) (inputs i) = Zmod.unsigned (N.v51088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51088 s i)) at 1.
  unfold R.v51088, N.v51088.
  rewrite ?node_51086.
  rewrite ?node_51087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51089 (s : N.State) (i : N.Inputs) :
  R.v51089 (state s) (inputs i) = Zmod.unsigned (N.v51089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51089 s i)) at 1.
  unfold R.v51089, N.v51089.
  unfold R.v16484, N.v16484.
  rewrite ?node_51088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51090 (s : N.State) (i : N.Inputs) :
  R.v51090 (state s) (inputs i) = Zmod.unsigned (N.v51090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51090 s i)) at 1.
  unfold R.v51090, N.v51090.
  rewrite ?node_51085.
  rewrite ?node_51089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51091 (s : N.State) (i : N.Inputs) :
  R.v51091 (state s) (inputs i) = Zmod.unsigned (N.v51091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51091 s i)) at 1.
  unfold R.v51091, N.v51091.
  unfold R.v6, N.v6.
  rewrite ?node_51090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51092 (s : N.State) (i : N.Inputs) :
  R.v51092 (state s) (inputs i) = Zmod.unsigned (N.v51092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51092 s i)) at 1.
  unfold R.v51092, N.v51092.
  rewrite ?node_10056.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51093 (s : N.State) (i : N.Inputs) :
  R.v51093 (state s) (inputs i) = Zmod.unsigned (N.v51093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51093 s i)) at 1.
  unfold R.v51093, N.v51093.
  unfold R.v6, N.v6.
  rewrite ?node_10234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51094 (s : N.State) (i : N.Inputs) :
  R.v51094 (state s) (inputs i) = Zmod.unsigned (N.v51094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51094 s i)) at 1.
  unfold R.v51094, N.v51094.
  rewrite ?node_51092.
  rewrite ?node_51093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51095 (s : N.State) (i : N.Inputs) :
  R.v51095 (state s) (inputs i) = Zmod.unsigned (N.v51095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51095 s i)) at 1.
  unfold R.v51095, N.v51095.
  rewrite ?node_51091.
  rewrite ?node_51094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51096 (s : N.State) (i : N.Inputs) :
  R.v51096 (state s) (inputs i) = Zmod.unsigned (N.v51096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51096 s i)) at 1.
  unfold R.v51096, N.v51096.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51097 (s : N.State) (i : N.Inputs) :
  R.v51097 (state s) (inputs i) = Zmod.unsigned (N.v51097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51097 s i)) at 1.
  unfold R.v51097, N.v51097.
  rewrite ?node_10079.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51098 (s : N.State) (i : N.Inputs) :
  R.v51098 (state s) (inputs i) = Zmod.unsigned (N.v51098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51098 s i)) at 1.
  unfold R.v51098, N.v51098.
  unfold R.v6, N.v6.
  rewrite ?node_10075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51099 (s : N.State) (i : N.Inputs) :
  R.v51099 (state s) (inputs i) = Zmod.unsigned (N.v51099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51099 s i)) at 1.
  unfold R.v51099, N.v51099.
  unfold R.v6, N.v6.
  rewrite ?node_10056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51100 (s : N.State) (i : N.Inputs) :
  R.v51100 (state s) (inputs i) = Zmod.unsigned (N.v51100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51100 s i)) at 1.
  unfold R.v51100, N.v51100.
  rewrite ?node_51098.
  rewrite ?node_51099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51101 (s : N.State) (i : N.Inputs) :
  R.v51101 (state s) (inputs i) = Zmod.unsigned (N.v51101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51101 s i)) at 1.
  unfold R.v51101, N.v51101.
  unfold R.v16484, N.v16484.
  rewrite ?node_51100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51102 (s : N.State) (i : N.Inputs) :
  R.v51102 (state s) (inputs i) = Zmod.unsigned (N.v51102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51102 s i)) at 1.
  unfold R.v51102, N.v51102.
  rewrite ?node_51097.
  rewrite ?node_51101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51103 (s : N.State) (i : N.Inputs) :
  R.v51103 (state s) (inputs i) = Zmod.unsigned (N.v51103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51103 s i)) at 1.
  unfold R.v51103, N.v51103.
  unfold R.v6, N.v6.
  rewrite ?node_51102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51104 (s : N.State) (i : N.Inputs) :
  R.v51104 (state s) (inputs i) = Zmod.unsigned (N.v51104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51104 s i)) at 1.
  unfold R.v51104, N.v51104.
  rewrite ?node_10080.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51105 (s : N.State) (i : N.Inputs) :
  R.v51105 (state s) (inputs i) = Zmod.unsigned (N.v51105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51105 s i)) at 1.
  unfold R.v51105, N.v51105.
  unfold R.v6, N.v6.
  rewrite ?node_10262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51106 (s : N.State) (i : N.Inputs) :
  R.v51106 (state s) (inputs i) = Zmod.unsigned (N.v51106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51106 s i)) at 1.
  unfold R.v51106, N.v51106.
  rewrite ?node_51104.
  rewrite ?node_51105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51107 (s : N.State) (i : N.Inputs) :
  R.v51107 (state s) (inputs i) = Zmod.unsigned (N.v51107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51107 s i)) at 1.
  unfold R.v51107, N.v51107.
  rewrite ?node_51103.
  rewrite ?node_51106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51108 (s : N.State) (i : N.Inputs) :
  R.v51108 (state s) (inputs i) = Zmod.unsigned (N.v51108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51108 s i)) at 1.
  unfold R.v51108, N.v51108.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51109 (s : N.State) (i : N.Inputs) :
  R.v51109 (state s) (inputs i) = Zmod.unsigned (N.v51109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51109 s i)) at 1.
  unfold R.v51109, N.v51109.
  rewrite ?node_10098.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51110 (s : N.State) (i : N.Inputs) :
  R.v51110 (state s) (inputs i) = Zmod.unsigned (N.v51110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51110 s i)) at 1.
  unfold R.v51110, N.v51110.
  rewrite ?node_10094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51111 (s : N.State) (i : N.Inputs) :
  R.v51111 (state s) (inputs i) = Zmod.unsigned (N.v51111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51111 s i)) at 1.
  unfold R.v51111, N.v51111.
  rewrite ?node_10090.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51112 (s : N.State) (i : N.Inputs) :
  R.v51112 (state s) (inputs i) = Zmod.unsigned (N.v51112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51112 s i)) at 1.
  unfold R.v51112, N.v51112.
  unfold R.v6, N.v6.
  rewrite ?node_10086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51113 (s : N.State) (i : N.Inputs) :
  R.v51113 (state s) (inputs i) = Zmod.unsigned (N.v51113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51113 s i)) at 1.
  unfold R.v51113, N.v51113.
  unfold R.v6, N.v6.
  rewrite ?node_10083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51114 (s : N.State) (i : N.Inputs) :
  R.v51114 (state s) (inputs i) = Zmod.unsigned (N.v51114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51114 s i)) at 1.
  unfold R.v51114, N.v51114.
  rewrite ?node_51112.
  rewrite ?node_51113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51115 (s : N.State) (i : N.Inputs) :
  R.v51115 (state s) (inputs i) = Zmod.unsigned (N.v51115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51115 s i)) at 1.
  unfold R.v51115, N.v51115.
  unfold R.v16484, N.v16484.
  rewrite ?node_51114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51116 (s : N.State) (i : N.Inputs) :
  R.v51116 (state s) (inputs i) = Zmod.unsigned (N.v51116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51116 s i)) at 1.
  unfold R.v51116, N.v51116.
  rewrite ?node_51109.
  rewrite ?node_51110.
  rewrite ?node_51111.
  rewrite ?node_51115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51117 (s : N.State) (i : N.Inputs) :
  R.v51117 (state s) (inputs i) = Zmod.unsigned (N.v51117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51117 s i)) at 1.
  unfold R.v51117, N.v51117.
  unfold R.v6, N.v6.
  rewrite ?node_51116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51118 (s : N.State) (i : N.Inputs) :
  R.v51118 (state s) (inputs i) = Zmod.unsigned (N.v51118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51118 s i)) at 1.
  unfold R.v51118, N.v51118.
  rewrite ?node_10099.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51119 (s : N.State) (i : N.Inputs) :
  R.v51119 (state s) (inputs i) = Zmod.unsigned (N.v51119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51119 s i)) at 1.
  unfold R.v51119, N.v51119.
  unfold R.v6, N.v6.
  rewrite ?node_10253.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51120 (s : N.State) (i : N.Inputs) :
  R.v51120 (state s) (inputs i) = Zmod.unsigned (N.v51120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51120 s i)) at 1.
  unfold R.v51120, N.v51120.
  unfold R.v6, N.v6.
  rewrite ?node_10270.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51121 (s : N.State) (i : N.Inputs) :
  R.v51121 (state s) (inputs i) = Zmod.unsigned (N.v51121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51121 s i)) at 1.
  unfold R.v51121, N.v51121.
  rewrite ?node_51118.
  rewrite ?node_51119.
  rewrite ?node_51120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51122 (s : N.State) (i : N.Inputs) :
  R.v51122 (state s) (inputs i) = Zmod.unsigned (N.v51122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51122 s i)) at 1.
  unfold R.v51122, N.v51122.
  rewrite ?node_51117.
  rewrite ?node_51121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51123 (s : N.State) (i : N.Inputs) :
  R.v51123 (state s) (inputs i) = Zmod.unsigned (N.v51123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51123 s i)) at 1.
  unfold R.v51123, N.v51123.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51124 (s : N.State) (i : N.Inputs) :
  R.v51124 (state s) (inputs i) = Zmod.unsigned (N.v51124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51124 s i)) at 1.
  unfold R.v51124, N.v51124.
  rewrite ?node_10090.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51125 (s : N.State) (i : N.Inputs) :
  R.v51125 (state s) (inputs i) = Zmod.unsigned (N.v51125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51125 s i)) at 1.
  unfold R.v51125, N.v51125.
  unfold R.v6, N.v6.
  rewrite ?node_10086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51126 (s : N.State) (i : N.Inputs) :
  R.v51126 (state s) (inputs i) = Zmod.unsigned (N.v51126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51126 s i)) at 1.
  unfold R.v51126, N.v51126.
  unfold R.v6, N.v6.
  rewrite ?node_10083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51127 (s : N.State) (i : N.Inputs) :
  R.v51127 (state s) (inputs i) = Zmod.unsigned (N.v51127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51127 s i)) at 1.
  unfold R.v51127, N.v51127.
  rewrite ?node_51125.
  rewrite ?node_51126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51128 (s : N.State) (i : N.Inputs) :
  R.v51128 (state s) (inputs i) = Zmod.unsigned (N.v51128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51128 s i)) at 1.
  unfold R.v51128, N.v51128.
  unfold R.v16484, N.v16484.
  rewrite ?node_51127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51129 (s : N.State) (i : N.Inputs) :
  R.v51129 (state s) (inputs i) = Zmod.unsigned (N.v51129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51129 s i)) at 1.
  unfold R.v51129, N.v51129.
  rewrite ?node_51124.
  rewrite ?node_51128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51130 (s : N.State) (i : N.Inputs) :
  R.v51130 (state s) (inputs i) = Zmod.unsigned (N.v51130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51130 s i)) at 1.
  unfold R.v51130, N.v51130.
  unfold R.v6, N.v6.
  rewrite ?node_51129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51131 (s : N.State) (i : N.Inputs) :
  R.v51131 (state s) (inputs i) = Zmod.unsigned (N.v51131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51131 s i)) at 1.
  unfold R.v51131, N.v51131.
  rewrite ?node_10091.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51132 (s : N.State) (i : N.Inputs) :
  R.v51132 (state s) (inputs i) = Zmod.unsigned (N.v51132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51132 s i)) at 1.
  unfold R.v51132, N.v51132.
  unfold R.v6, N.v6.
  rewrite ?node_10253.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51133 (s : N.State) (i : N.Inputs) :
  R.v51133 (state s) (inputs i) = Zmod.unsigned (N.v51133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51133 s i)) at 1.
  unfold R.v51133, N.v51133.
  rewrite ?node_51131.
  rewrite ?node_51132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51134 (s : N.State) (i : N.Inputs) :
  R.v51134 (state s) (inputs i) = Zmod.unsigned (N.v51134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51134 s i)) at 1.
  unfold R.v51134, N.v51134.
  rewrite ?node_51130.
  rewrite ?node_51133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51135 (s : N.State) (i : N.Inputs) :
  R.v51135 (state s) (inputs i) = Zmod.unsigned (N.v51135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51135 s i)) at 1.
  unfold R.v51135, N.v51135.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51136 (s : N.State) (i : N.Inputs) :
  R.v51136 (state s) (inputs i) = Zmod.unsigned (N.v51136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51136 s i)) at 1.
  unfold R.v51136, N.v51136.
  rewrite ?node_10098.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51137 (s : N.State) (i : N.Inputs) :
  R.v51137 (state s) (inputs i) = Zmod.unsigned (N.v51137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51137 s i)) at 1.
  unfold R.v51137, N.v51137.
  unfold R.v6, N.v6.
  rewrite ?node_10094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51138 (s : N.State) (i : N.Inputs) :
  R.v51138 (state s) (inputs i) = Zmod.unsigned (N.v51138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51138 s i)) at 1.
  unfold R.v51138, N.v51138.
  unfold R.v6, N.v6.
  rewrite ?node_10091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51139 (s : N.State) (i : N.Inputs) :
  R.v51139 (state s) (inputs i) = Zmod.unsigned (N.v51139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51139 s i)) at 1.
  unfold R.v51139, N.v51139.
  rewrite ?node_51137.
  rewrite ?node_51138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51140 (s : N.State) (i : N.Inputs) :
  R.v51140 (state s) (inputs i) = Zmod.unsigned (N.v51140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51140 s i)) at 1.
  unfold R.v51140, N.v51140.
  unfold R.v16484, N.v16484.
  rewrite ?node_51139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51141 (s : N.State) (i : N.Inputs) :
  R.v51141 (state s) (inputs i) = Zmod.unsigned (N.v51141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51141 s i)) at 1.
  unfold R.v51141, N.v51141.
  rewrite ?node_51136.
  rewrite ?node_51140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51142 (s : N.State) (i : N.Inputs) :
  R.v51142 (state s) (inputs i) = Zmod.unsigned (N.v51142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51142 s i)) at 1.
  unfold R.v51142, N.v51142.
  unfold R.v6, N.v6.
  rewrite ?node_51141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51143 (s : N.State) (i : N.Inputs) :
  R.v51143 (state s) (inputs i) = Zmod.unsigned (N.v51143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51143 s i)) at 1.
  unfold R.v51143, N.v51143.
  rewrite ?node_10099.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51144 (s : N.State) (i : N.Inputs) :
  R.v51144 (state s) (inputs i) = Zmod.unsigned (N.v51144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51144 s i)) at 1.
  unfold R.v51144, N.v51144.
  unfold R.v6, N.v6.
  rewrite ?node_10270.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51145 (s : N.State) (i : N.Inputs) :
  R.v51145 (state s) (inputs i) = Zmod.unsigned (N.v51145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51145 s i)) at 1.
  unfold R.v51145, N.v51145.
  rewrite ?node_51143.
  rewrite ?node_51144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51146 (s : N.State) (i : N.Inputs) :
  R.v51146 (state s) (inputs i) = Zmod.unsigned (N.v51146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51146 s i)) at 1.
  unfold R.v51146, N.v51146.
  rewrite ?node_51142.
  rewrite ?node_51145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51147 (s : N.State) (i : N.Inputs) :
  R.v51147 (state s) (inputs i) = Zmod.unsigned (N.v51147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51147 s i)) at 1.
  unfold R.v51147, N.v51147.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51148 (s : N.State) (i : N.Inputs) :
  R.v51148 (state s) (inputs i) = Zmod.unsigned (N.v51148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51148 s i)) at 1.
  unfold R.v51148, N.v51148.
  rewrite ?node_10234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51149 (s : N.State) (i : N.Inputs) :
  R.v51149 (state s) (inputs i) = Zmod.unsigned (N.v51149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51149 s i)) at 1.
  unfold R.v51149, N.v51149.
  rewrite ?node_10230.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51150 (s : N.State) (i : N.Inputs) :
  R.v51150 (state s) (inputs i) = Zmod.unsigned (N.v51150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51150 s i)) at 1.
  unfold R.v51150, N.v51150.
  rewrite ?node_10210.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51151 (s : N.State) (i : N.Inputs) :
  R.v51151 (state s) (inputs i) = Zmod.unsigned (N.v51151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51151 s i)) at 1.
  unfold R.v51151, N.v51151.
  unfold R.v6, N.v6.
  rewrite ?node_10193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51152 (s : N.State) (i : N.Inputs) :
  R.v51152 (state s) (inputs i) = Zmod.unsigned (N.v51152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51152 s i)) at 1.
  unfold R.v51152, N.v51152.
  unfold R.v6, N.v6.
  rewrite ?node_10158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51153 (s : N.State) (i : N.Inputs) :
  R.v51153 (state s) (inputs i) = Zmod.unsigned (N.v51153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51153 s i)) at 1.
  unfold R.v51153, N.v51153.
  rewrite ?node_51151.
  rewrite ?node_51152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51154 (s : N.State) (i : N.Inputs) :
  R.v51154 (state s) (inputs i) = Zmod.unsigned (N.v51154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51154 s i)) at 1.
  unfold R.v51154, N.v51154.
  unfold R.v16484, N.v16484.
  rewrite ?node_51153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51155 (s : N.State) (i : N.Inputs) :
  R.v51155 (state s) (inputs i) = Zmod.unsigned (N.v51155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51155 s i)) at 1.
  unfold R.v51155, N.v51155.
  rewrite ?node_51148.
  rewrite ?node_51149.
  rewrite ?node_51150.
  rewrite ?node_51154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51156 (s : N.State) (i : N.Inputs) :
  R.v51156 (state s) (inputs i) = Zmod.unsigned (N.v51156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51156 s i)) at 1.
  unfold R.v51156, N.v51156.
  unfold R.v6, N.v6.
  rewrite ?node_51155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51157 (s : N.State) (i : N.Inputs) :
  R.v51157 (state s) (inputs i) = Zmod.unsigned (N.v51157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51157 s i)) at 1.
  unfold R.v51157, N.v51157.
  rewrite ?node_10235.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51158 (s : N.State) (i : N.Inputs) :
  R.v51158 (state s) (inputs i) = Zmod.unsigned (N.v51158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51158 s i)) at 1.
  unfold R.v51158, N.v51158.
  unfold R.v6, N.v6.
  rewrite ?node_10392.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51159 (s : N.State) (i : N.Inputs) :
  R.v51159 (state s) (inputs i) = Zmod.unsigned (N.v51159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51159 s i)) at 1.
  unfold R.v51159, N.v51159.
  unfold R.v6, N.v6.
  rewrite ?node_10420.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51160 (s : N.State) (i : N.Inputs) :
  R.v51160 (state s) (inputs i) = Zmod.unsigned (N.v51160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51160 s i)) at 1.
  unfold R.v51160, N.v51160.
  rewrite ?node_51157.
  rewrite ?node_51158.
  rewrite ?node_51159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51161 (s : N.State) (i : N.Inputs) :
  R.v51161 (state s) (inputs i) = Zmod.unsigned (N.v51161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51161 s i)) at 1.
  unfold R.v51161, N.v51161.
  rewrite ?node_51156.
  rewrite ?node_51160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51162 (s : N.State) (i : N.Inputs) :
  R.v51162 (state s) (inputs i) = Zmod.unsigned (N.v51162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51162 s i)) at 1.
  unfold R.v51162, N.v51162.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51163 (s : N.State) (i : N.Inputs) :
  R.v51163 (state s) (inputs i) = Zmod.unsigned (N.v51163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51163 s i)) at 1.
  unfold R.v51163, N.v51163.
  rewrite ?node_10210.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51164 (s : N.State) (i : N.Inputs) :
  R.v51164 (state s) (inputs i) = Zmod.unsigned (N.v51164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51164 s i)) at 1.
  unfold R.v51164, N.v51164.
  unfold R.v6, N.v6.
  rewrite ?node_10193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51165 (s : N.State) (i : N.Inputs) :
  R.v51165 (state s) (inputs i) = Zmod.unsigned (N.v51165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51165 s i)) at 1.
  unfold R.v51165, N.v51165.
  unfold R.v6, N.v6.
  rewrite ?node_10158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51166 (s : N.State) (i : N.Inputs) :
  R.v51166 (state s) (inputs i) = Zmod.unsigned (N.v51166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51166 s i)) at 1.
  unfold R.v51166, N.v51166.
  rewrite ?node_51164.
  rewrite ?node_51165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51167 (s : N.State) (i : N.Inputs) :
  R.v51167 (state s) (inputs i) = Zmod.unsigned (N.v51167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51167 s i)) at 1.
  unfold R.v51167, N.v51167.
  unfold R.v16484, N.v16484.
  rewrite ?node_51166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51168 (s : N.State) (i : N.Inputs) :
  R.v51168 (state s) (inputs i) = Zmod.unsigned (N.v51168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51168 s i)) at 1.
  unfold R.v51168, N.v51168.
  rewrite ?node_51163.
  rewrite ?node_51167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51169 (s : N.State) (i : N.Inputs) :
  R.v51169 (state s) (inputs i) = Zmod.unsigned (N.v51169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51169 s i)) at 1.
  unfold R.v51169, N.v51169.
  unfold R.v6, N.v6.
  rewrite ?node_51168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51170 (s : N.State) (i : N.Inputs) :
  R.v51170 (state s) (inputs i) = Zmod.unsigned (N.v51170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51170 s i)) at 1.
  unfold R.v51170, N.v51170.
  rewrite ?node_10211.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51171 (s : N.State) (i : N.Inputs) :
  R.v51171 (state s) (inputs i) = Zmod.unsigned (N.v51171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51171 s i)) at 1.
  unfold R.v51171, N.v51171.
  unfold R.v6, N.v6.
  rewrite ?node_10392.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51172 (s : N.State) (i : N.Inputs) :
  R.v51172 (state s) (inputs i) = Zmod.unsigned (N.v51172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51172 s i)) at 1.
  unfold R.v51172, N.v51172.
  rewrite ?node_51170.
  rewrite ?node_51171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51173 (s : N.State) (i : N.Inputs) :
  R.v51173 (state s) (inputs i) = Zmod.unsigned (N.v51173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51173 s i)) at 1.
  unfold R.v51173, N.v51173.
  rewrite ?node_51169.
  rewrite ?node_51172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51174 (s : N.State) (i : N.Inputs) :
  R.v51174 (state s) (inputs i) = Zmod.unsigned (N.v51174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51174 s i)) at 1.
  unfold R.v51174, N.v51174.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51175 (s : N.State) (i : N.Inputs) :
  R.v51175 (state s) (inputs i) = Zmod.unsigned (N.v51175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51175 s i)) at 1.
  unfold R.v51175, N.v51175.
  rewrite ?node_10234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51176 (s : N.State) (i : N.Inputs) :
  R.v51176 (state s) (inputs i) = Zmod.unsigned (N.v51176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51176 s i)) at 1.
  unfold R.v51176, N.v51176.
  unfold R.v6, N.v6.
  rewrite ?node_10230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51177 (s : N.State) (i : N.Inputs) :
  R.v51177 (state s) (inputs i) = Zmod.unsigned (N.v51177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51177 s i)) at 1.
  unfold R.v51177, N.v51177.
  unfold R.v6, N.v6.
  rewrite ?node_10211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51178 (s : N.State) (i : N.Inputs) :
  R.v51178 (state s) (inputs i) = Zmod.unsigned (N.v51178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51178 s i)) at 1.
  unfold R.v51178, N.v51178.
  rewrite ?node_51176.
  rewrite ?node_51177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51179 (s : N.State) (i : N.Inputs) :
  R.v51179 (state s) (inputs i) = Zmod.unsigned (N.v51179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51179 s i)) at 1.
  unfold R.v51179, N.v51179.
  unfold R.v16484, N.v16484.
  rewrite ?node_51178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51180 (s : N.State) (i : N.Inputs) :
  R.v51180 (state s) (inputs i) = Zmod.unsigned (N.v51180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51180 s i)) at 1.
  unfold R.v51180, N.v51180.
  rewrite ?node_51175.
  rewrite ?node_51179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51181 (s : N.State) (i : N.Inputs) :
  R.v51181 (state s) (inputs i) = Zmod.unsigned (N.v51181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51181 s i)) at 1.
  unfold R.v51181, N.v51181.
  unfold R.v6, N.v6.
  rewrite ?node_51180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51182 (s : N.State) (i : N.Inputs) :
  R.v51182 (state s) (inputs i) = Zmod.unsigned (N.v51182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51182 s i)) at 1.
  unfold R.v51182, N.v51182.
  rewrite ?node_10235.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51183 (s : N.State) (i : N.Inputs) :
  R.v51183 (state s) (inputs i) = Zmod.unsigned (N.v51183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51183 s i)) at 1.
  unfold R.v51183, N.v51183.
  unfold R.v6, N.v6.
  rewrite ?node_10420.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51184 (s : N.State) (i : N.Inputs) :
  R.v51184 (state s) (inputs i) = Zmod.unsigned (N.v51184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51184 s i)) at 1.
  unfold R.v51184, N.v51184.
  rewrite ?node_51182.
  rewrite ?node_51183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51185 (s : N.State) (i : N.Inputs) :
  R.v51185 (state s) (inputs i) = Zmod.unsigned (N.v51185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51185 s i)) at 1.
  unfold R.v51185, N.v51185.
  rewrite ?node_51181.
  rewrite ?node_51184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51186 (s : N.State) (i : N.Inputs) :
  R.v51186 (state s) (inputs i) = Zmod.unsigned (N.v51186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51186 s i)) at 1.
  unfold R.v51186, N.v51186.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51187 (s : N.State) (i : N.Inputs) :
  R.v51187 (state s) (inputs i) = Zmod.unsigned (N.v51187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51187 s i)) at 1.
  unfold R.v51187, N.v51187.
  rewrite ?node_10253.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51188 (s : N.State) (i : N.Inputs) :
  R.v51188 (state s) (inputs i) = Zmod.unsigned (N.v51188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51188 s i)) at 1.
  unfold R.v51188, N.v51188.
  rewrite ?node_10249.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51189 (s : N.State) (i : N.Inputs) :
  R.v51189 (state s) (inputs i) = Zmod.unsigned (N.v51189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51189 s i)) at 1.
  unfold R.v51189, N.v51189.
  rewrite ?node_10245.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51190 (s : N.State) (i : N.Inputs) :
  R.v51190 (state s) (inputs i) = Zmod.unsigned (N.v51190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51190 s i)) at 1.
  unfold R.v51190, N.v51190.
  unfold R.v6, N.v6.
  rewrite ?node_10241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51191 (s : N.State) (i : N.Inputs) :
  R.v51191 (state s) (inputs i) = Zmod.unsigned (N.v51191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51191 s i)) at 1.
  unfold R.v51191, N.v51191.
  unfold R.v6, N.v6.
  rewrite ?node_10238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51192 (s : N.State) (i : N.Inputs) :
  R.v51192 (state s) (inputs i) = Zmod.unsigned (N.v51192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51192 s i)) at 1.
  unfold R.v51192, N.v51192.
  rewrite ?node_51190.
  rewrite ?node_51191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51193 (s : N.State) (i : N.Inputs) :
  R.v51193 (state s) (inputs i) = Zmod.unsigned (N.v51193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51193 s i)) at 1.
  unfold R.v51193, N.v51193.
  unfold R.v16484, N.v16484.
  rewrite ?node_51192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51194 (s : N.State) (i : N.Inputs) :
  R.v51194 (state s) (inputs i) = Zmod.unsigned (N.v51194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51194 s i)) at 1.
  unfold R.v51194, N.v51194.
  rewrite ?node_51187.
  rewrite ?node_51188.
  rewrite ?node_51189.
  rewrite ?node_51193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51195 (s : N.State) (i : N.Inputs) :
  R.v51195 (state s) (inputs i) = Zmod.unsigned (N.v51195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51195 s i)) at 1.
  unfold R.v51195, N.v51195.
  unfold R.v6, N.v6.
  rewrite ?node_51194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51196 (s : N.State) (i : N.Inputs) :
  R.v51196 (state s) (inputs i) = Zmod.unsigned (N.v51196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51196 s i)) at 1.
  unfold R.v51196, N.v51196.
  rewrite ?node_10254.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51197 (s : N.State) (i : N.Inputs) :
  R.v51197 (state s) (inputs i) = Zmod.unsigned (N.v51197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51197 s i)) at 1.
  unfold R.v51197, N.v51197.
  unfold R.v6, N.v6.
  rewrite ?node_10411.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51198 (s : N.State) (i : N.Inputs) :
  R.v51198 (state s) (inputs i) = Zmod.unsigned (N.v51198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51198 s i)) at 1.
  unfold R.v51198, N.v51198.
  unfold R.v6, N.v6.
  rewrite ?node_10428.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51199 (s : N.State) (i : N.Inputs) :
  R.v51199 (state s) (inputs i) = Zmod.unsigned (N.v51199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51199 s i)) at 1.
  unfold R.v51199, N.v51199.
  rewrite ?node_51196.
  rewrite ?node_51197.
  rewrite ?node_51198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51200 (s : N.State) (i : N.Inputs) :
  R.v51200 (state s) (inputs i) = Zmod.unsigned (N.v51200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51200 s i)) at 1.
  unfold R.v51200, N.v51200.
  rewrite ?node_51195.
  rewrite ?node_51199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51201 (s : N.State) (i : N.Inputs) :
  R.v51201 (state s) (inputs i) = Zmod.unsigned (N.v51201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51201 s i)) at 1.
  unfold R.v51201, N.v51201.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51202 (s : N.State) (i : N.Inputs) :
  R.v51202 (state s) (inputs i) = Zmod.unsigned (N.v51202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51202 s i)) at 1.
  unfold R.v51202, N.v51202.
  rewrite ?node_10245.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51203 (s : N.State) (i : N.Inputs) :
  R.v51203 (state s) (inputs i) = Zmod.unsigned (N.v51203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51203 s i)) at 1.
  unfold R.v51203, N.v51203.
  unfold R.v6, N.v6.
  rewrite ?node_10241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51204 (s : N.State) (i : N.Inputs) :
  R.v51204 (state s) (inputs i) = Zmod.unsigned (N.v51204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51204 s i)) at 1.
  unfold R.v51204, N.v51204.
  unfold R.v6, N.v6.
  rewrite ?node_10238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51205 (s : N.State) (i : N.Inputs) :
  R.v51205 (state s) (inputs i) = Zmod.unsigned (N.v51205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51205 s i)) at 1.
  unfold R.v51205, N.v51205.
  rewrite ?node_51203.
  rewrite ?node_51204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51206 (s : N.State) (i : N.Inputs) :
  R.v51206 (state s) (inputs i) = Zmod.unsigned (N.v51206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51206 s i)) at 1.
  unfold R.v51206, N.v51206.
  unfold R.v16484, N.v16484.
  rewrite ?node_51205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51207 (s : N.State) (i : N.Inputs) :
  R.v51207 (state s) (inputs i) = Zmod.unsigned (N.v51207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51207 s i)) at 1.
  unfold R.v51207, N.v51207.
  rewrite ?node_51202.
  rewrite ?node_51206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51208 (s : N.State) (i : N.Inputs) :
  R.v51208 (state s) (inputs i) = Zmod.unsigned (N.v51208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51208 s i)) at 1.
  unfold R.v51208, N.v51208.
  unfold R.v6, N.v6.
  rewrite ?node_51207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51209 (s : N.State) (i : N.Inputs) :
  R.v51209 (state s) (inputs i) = Zmod.unsigned (N.v51209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51209 s i)) at 1.
  unfold R.v51209, N.v51209.
  rewrite ?node_10246.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51210 (s : N.State) (i : N.Inputs) :
  R.v51210 (state s) (inputs i) = Zmod.unsigned (N.v51210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51210 s i)) at 1.
  unfold R.v51210, N.v51210.
  unfold R.v6, N.v6.
  rewrite ?node_10411.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51211 (s : N.State) (i : N.Inputs) :
  R.v51211 (state s) (inputs i) = Zmod.unsigned (N.v51211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51211 s i)) at 1.
  unfold R.v51211, N.v51211.
  rewrite ?node_51209.
  rewrite ?node_51210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51212 (s : N.State) (i : N.Inputs) :
  R.v51212 (state s) (inputs i) = Zmod.unsigned (N.v51212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51212 s i)) at 1.
  unfold R.v51212, N.v51212.
  rewrite ?node_51208.
  rewrite ?node_51211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51213 (s : N.State) (i : N.Inputs) :
  R.v51213 (state s) (inputs i) = Zmod.unsigned (N.v51213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51213 s i)) at 1.
  unfold R.v51213, N.v51213.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51214 (s : N.State) (i : N.Inputs) :
  R.v51214 (state s) (inputs i) = Zmod.unsigned (N.v51214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51214 s i)) at 1.
  unfold R.v51214, N.v51214.
  rewrite ?node_10253.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51215 (s : N.State) (i : N.Inputs) :
  R.v51215 (state s) (inputs i) = Zmod.unsigned (N.v51215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51215 s i)) at 1.
  unfold R.v51215, N.v51215.
  unfold R.v6, N.v6.
  rewrite ?node_10249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51216 (s : N.State) (i : N.Inputs) :
  R.v51216 (state s) (inputs i) = Zmod.unsigned (N.v51216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51216 s i)) at 1.
  unfold R.v51216, N.v51216.
  unfold R.v6, N.v6.
  rewrite ?node_10246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51217 (s : N.State) (i : N.Inputs) :
  R.v51217 (state s) (inputs i) = Zmod.unsigned (N.v51217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51217 s i)) at 1.
  unfold R.v51217, N.v51217.
  rewrite ?node_51215.
  rewrite ?node_51216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51218 (s : N.State) (i : N.Inputs) :
  R.v51218 (state s) (inputs i) = Zmod.unsigned (N.v51218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51218 s i)) at 1.
  unfold R.v51218, N.v51218.
  unfold R.v16484, N.v16484.
  rewrite ?node_51217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51219 (s : N.State) (i : N.Inputs) :
  R.v51219 (state s) (inputs i) = Zmod.unsigned (N.v51219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51219 s i)) at 1.
  unfold R.v51219, N.v51219.
  rewrite ?node_51214.
  rewrite ?node_51218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51220 (s : N.State) (i : N.Inputs) :
  R.v51220 (state s) (inputs i) = Zmod.unsigned (N.v51220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51220 s i)) at 1.
  unfold R.v51220, N.v51220.
  unfold R.v6, N.v6.
  rewrite ?node_51219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51221 (s : N.State) (i : N.Inputs) :
  R.v51221 (state s) (inputs i) = Zmod.unsigned (N.v51221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51221 s i)) at 1.
  unfold R.v51221, N.v51221.
  rewrite ?node_10254.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51222 (s : N.State) (i : N.Inputs) :
  R.v51222 (state s) (inputs i) = Zmod.unsigned (N.v51222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51222 s i)) at 1.
  unfold R.v51222, N.v51222.
  unfold R.v6, N.v6.
  rewrite ?node_10428.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51223 (s : N.State) (i : N.Inputs) :
  R.v51223 (state s) (inputs i) = Zmod.unsigned (N.v51223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51223 s i)) at 1.
  unfold R.v51223, N.v51223.
  rewrite ?node_51221.
  rewrite ?node_51222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51224 (s : N.State) (i : N.Inputs) :
  R.v51224 (state s) (inputs i) = Zmod.unsigned (N.v51224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51224 s i)) at 1.
  unfold R.v51224, N.v51224.
  rewrite ?node_51220.
  rewrite ?node_51223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51225 (s : N.State) (i : N.Inputs) :
  R.v51225 (state s) (inputs i) = Zmod.unsigned (N.v51225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51225 s i)) at 1.
  unfold R.v51225, N.v51225.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51226 (s : N.State) (i : N.Inputs) :
  R.v51226 (state s) (inputs i) = Zmod.unsigned (N.v51226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51226 s i)) at 1.
  unfold R.v51226, N.v51226.
  rewrite ?node_10392.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51227 (s : N.State) (i : N.Inputs) :
  R.v51227 (state s) (inputs i) = Zmod.unsigned (N.v51227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51227 s i)) at 1.
  unfold R.v51227, N.v51227.
  rewrite ?node_10388.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51228 (s : N.State) (i : N.Inputs) :
  R.v51228 (state s) (inputs i) = Zmod.unsigned (N.v51228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51228 s i)) at 1.
  unfold R.v51228, N.v51228.
  rewrite ?node_10368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51229 (s : N.State) (i : N.Inputs) :
  R.v51229 (state s) (inputs i) = Zmod.unsigned (N.v51229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51229 s i)) at 1.
  unfold R.v51229, N.v51229.
  unfold R.v6, N.v6.
  rewrite ?node_10350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51230 (s : N.State) (i : N.Inputs) :
  R.v51230 (state s) (inputs i) = Zmod.unsigned (N.v51230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51230 s i)) at 1.
  unfold R.v51230, N.v51230.
  unfold R.v6, N.v6.
  rewrite ?node_10315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51231 (s : N.State) (i : N.Inputs) :
  R.v51231 (state s) (inputs i) = Zmod.unsigned (N.v51231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51231 s i)) at 1.
  unfold R.v51231, N.v51231.
  rewrite ?node_51229.
  rewrite ?node_51230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51232 (s : N.State) (i : N.Inputs) :
  R.v51232 (state s) (inputs i) = Zmod.unsigned (N.v51232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51232 s i)) at 1.
  unfold R.v51232, N.v51232.
  unfold R.v16484, N.v16484.
  rewrite ?node_51231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51233 (s : N.State) (i : N.Inputs) :
  R.v51233 (state s) (inputs i) = Zmod.unsigned (N.v51233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51233 s i)) at 1.
  unfold R.v51233, N.v51233.
  rewrite ?node_51226.
  rewrite ?node_51227.
  rewrite ?node_51228.
  rewrite ?node_51232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51234 (s : N.State) (i : N.Inputs) :
  R.v51234 (state s) (inputs i) = Zmod.unsigned (N.v51234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51234 s i)) at 1.
  unfold R.v51234, N.v51234.
  unfold R.v6, N.v6.
  rewrite ?node_51233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51235 (s : N.State) (i : N.Inputs) :
  R.v51235 (state s) (inputs i) = Zmod.unsigned (N.v51235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51235 s i)) at 1.
  unfold R.v51235, N.v51235.
  rewrite ?node_10393.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51236 (s : N.State) (i : N.Inputs) :
  R.v51236 (state s) (inputs i) = Zmod.unsigned (N.v51236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51236 s i)) at 1.
  unfold R.v51236, N.v51236.
  unfold R.v6, N.v6.
  rewrite ?node_10550.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51237 (s : N.State) (i : N.Inputs) :
  R.v51237 (state s) (inputs i) = Zmod.unsigned (N.v51237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51237 s i)) at 1.
  unfold R.v51237, N.v51237.
  unfold R.v6, N.v6.
  rewrite ?node_10580.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51238 (s : N.State) (i : N.Inputs) :
  R.v51238 (state s) (inputs i) = Zmod.unsigned (N.v51238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51238 s i)) at 1.
  unfold R.v51238, N.v51238.
  rewrite ?node_51235.
  rewrite ?node_51236.
  rewrite ?node_51237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51239 (s : N.State) (i : N.Inputs) :
  R.v51239 (state s) (inputs i) = Zmod.unsigned (N.v51239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51239 s i)) at 1.
  unfold R.v51239, N.v51239.
  rewrite ?node_51234.
  rewrite ?node_51238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51240 (s : N.State) (i : N.Inputs) :
  R.v51240 (state s) (inputs i) = Zmod.unsigned (N.v51240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51240 s i)) at 1.
  unfold R.v51240, N.v51240.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51241 (s : N.State) (i : N.Inputs) :
  R.v51241 (state s) (inputs i) = Zmod.unsigned (N.v51241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51241 s i)) at 1.
  unfold R.v51241, N.v51241.
  rewrite ?node_10368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51242 (s : N.State) (i : N.Inputs) :
  R.v51242 (state s) (inputs i) = Zmod.unsigned (N.v51242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51242 s i)) at 1.
  unfold R.v51242, N.v51242.
  unfold R.v6, N.v6.
  rewrite ?node_10350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51243 (s : N.State) (i : N.Inputs) :
  R.v51243 (state s) (inputs i) = Zmod.unsigned (N.v51243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51243 s i)) at 1.
  unfold R.v51243, N.v51243.
  unfold R.v6, N.v6.
  rewrite ?node_10315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51244 (s : N.State) (i : N.Inputs) :
  R.v51244 (state s) (inputs i) = Zmod.unsigned (N.v51244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51244 s i)) at 1.
  unfold R.v51244, N.v51244.
  rewrite ?node_51242.
  rewrite ?node_51243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51245 (s : N.State) (i : N.Inputs) :
  R.v51245 (state s) (inputs i) = Zmod.unsigned (N.v51245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51245 s i)) at 1.
  unfold R.v51245, N.v51245.
  unfold R.v16484, N.v16484.
  rewrite ?node_51244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51246 (s : N.State) (i : N.Inputs) :
  R.v51246 (state s) (inputs i) = Zmod.unsigned (N.v51246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51246 s i)) at 1.
  unfold R.v51246, N.v51246.
  rewrite ?node_51241.
  rewrite ?node_51245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51247 (s : N.State) (i : N.Inputs) :
  R.v51247 (state s) (inputs i) = Zmod.unsigned (N.v51247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51247 s i)) at 1.
  unfold R.v51247, N.v51247.
  unfold R.v6, N.v6.
  rewrite ?node_51246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51248 (s : N.State) (i : N.Inputs) :
  R.v51248 (state s) (inputs i) = Zmod.unsigned (N.v51248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51248 s i)) at 1.
  unfold R.v51248, N.v51248.
  rewrite ?node_10369.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51249 (s : N.State) (i : N.Inputs) :
  R.v51249 (state s) (inputs i) = Zmod.unsigned (N.v51249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51249 s i)) at 1.
  unfold R.v51249, N.v51249.
  unfold R.v6, N.v6.
  rewrite ?node_10550.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51250 (s : N.State) (i : N.Inputs) :
  R.v51250 (state s) (inputs i) = Zmod.unsigned (N.v51250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51250 s i)) at 1.
  unfold R.v51250, N.v51250.
  rewrite ?node_51248.
  rewrite ?node_51249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51251 (s : N.State) (i : N.Inputs) :
  R.v51251 (state s) (inputs i) = Zmod.unsigned (N.v51251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51251 s i)) at 1.
  unfold R.v51251, N.v51251.
  rewrite ?node_51247.
  rewrite ?node_51250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51252 (s : N.State) (i : N.Inputs) :
  R.v51252 (state s) (inputs i) = Zmod.unsigned (N.v51252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51252 s i)) at 1.
  unfold R.v51252, N.v51252.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51253 (s : N.State) (i : N.Inputs) :
  R.v51253 (state s) (inputs i) = Zmod.unsigned (N.v51253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51253 s i)) at 1.
  unfold R.v51253, N.v51253.
  rewrite ?node_10392.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51254 (s : N.State) (i : N.Inputs) :
  R.v51254 (state s) (inputs i) = Zmod.unsigned (N.v51254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51254 s i)) at 1.
  unfold R.v51254, N.v51254.
  unfold R.v6, N.v6.
  rewrite ?node_10388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51255 (s : N.State) (i : N.Inputs) :
  R.v51255 (state s) (inputs i) = Zmod.unsigned (N.v51255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51255 s i)) at 1.
  unfold R.v51255, N.v51255.
  unfold R.v6, N.v6.
  rewrite ?node_10369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51256 (s : N.State) (i : N.Inputs) :
  R.v51256 (state s) (inputs i) = Zmod.unsigned (N.v51256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51256 s i)) at 1.
  unfold R.v51256, N.v51256.
  rewrite ?node_51254.
  rewrite ?node_51255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51257 (s : N.State) (i : N.Inputs) :
  R.v51257 (state s) (inputs i) = Zmod.unsigned (N.v51257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51257 s i)) at 1.
  unfold R.v51257, N.v51257.
  unfold R.v16484, N.v16484.
  rewrite ?node_51256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51258 (s : N.State) (i : N.Inputs) :
  R.v51258 (state s) (inputs i) = Zmod.unsigned (N.v51258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51258 s i)) at 1.
  unfold R.v51258, N.v51258.
  rewrite ?node_51253.
  rewrite ?node_51257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51259 (s : N.State) (i : N.Inputs) :
  R.v51259 (state s) (inputs i) = Zmod.unsigned (N.v51259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51259 s i)) at 1.
  unfold R.v51259, N.v51259.
  unfold R.v6, N.v6.
  rewrite ?node_51258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51260 (s : N.State) (i : N.Inputs) :
  R.v51260 (state s) (inputs i) = Zmod.unsigned (N.v51260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51260 s i)) at 1.
  unfold R.v51260, N.v51260.
  rewrite ?node_10393.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51261 (s : N.State) (i : N.Inputs) :
  R.v51261 (state s) (inputs i) = Zmod.unsigned (N.v51261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51261 s i)) at 1.
  unfold R.v51261, N.v51261.
  unfold R.v6, N.v6.
  rewrite ?node_10580.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51262 (s : N.State) (i : N.Inputs) :
  R.v51262 (state s) (inputs i) = Zmod.unsigned (N.v51262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51262 s i)) at 1.
  unfold R.v51262, N.v51262.
  rewrite ?node_51260.
  rewrite ?node_51261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51263 (s : N.State) (i : N.Inputs) :
  R.v51263 (state s) (inputs i) = Zmod.unsigned (N.v51263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51263 s i)) at 1.
  unfold R.v51263, N.v51263.
  rewrite ?node_51259.
  rewrite ?node_51262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51264 (s : N.State) (i : N.Inputs) :
  R.v51264 (state s) (inputs i) = Zmod.unsigned (N.v51264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51264 s i)) at 1.
  unfold R.v51264, N.v51264.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51265 (s : N.State) (i : N.Inputs) :
  R.v51265 (state s) (inputs i) = Zmod.unsigned (N.v51265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51265 s i)) at 1.
  unfold R.v51265, N.v51265.
  rewrite ?node_10411.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51266 (s : N.State) (i : N.Inputs) :
  R.v51266 (state s) (inputs i) = Zmod.unsigned (N.v51266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51266 s i)) at 1.
  unfold R.v51266, N.v51266.
  rewrite ?node_10407.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51267 (s : N.State) (i : N.Inputs) :
  R.v51267 (state s) (inputs i) = Zmod.unsigned (N.v51267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51267 s i)) at 1.
  unfold R.v51267, N.v51267.
  rewrite ?node_10403.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51268 (s : N.State) (i : N.Inputs) :
  R.v51268 (state s) (inputs i) = Zmod.unsigned (N.v51268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51268 s i)) at 1.
  unfold R.v51268, N.v51268.
  unfold R.v6, N.v6.
  rewrite ?node_10399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51269 (s : N.State) (i : N.Inputs) :
  R.v51269 (state s) (inputs i) = Zmod.unsigned (N.v51269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51269 s i)) at 1.
  unfold R.v51269, N.v51269.
  unfold R.v6, N.v6.
  rewrite ?node_10396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51270 (s : N.State) (i : N.Inputs) :
  R.v51270 (state s) (inputs i) = Zmod.unsigned (N.v51270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51270 s i)) at 1.
  unfold R.v51270, N.v51270.
  rewrite ?node_51268.
  rewrite ?node_51269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51271 (s : N.State) (i : N.Inputs) :
  R.v51271 (state s) (inputs i) = Zmod.unsigned (N.v51271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51271 s i)) at 1.
  unfold R.v51271, N.v51271.
  unfold R.v16484, N.v16484.
  rewrite ?node_51270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51272 (s : N.State) (i : N.Inputs) :
  R.v51272 (state s) (inputs i) = Zmod.unsigned (N.v51272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51272 s i)) at 1.
  unfold R.v51272, N.v51272.
  rewrite ?node_51265.
  rewrite ?node_51266.
  rewrite ?node_51267.
  rewrite ?node_51271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51273 (s : N.State) (i : N.Inputs) :
  R.v51273 (state s) (inputs i) = Zmod.unsigned (N.v51273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51273 s i)) at 1.
  unfold R.v51273, N.v51273.
  unfold R.v6, N.v6.
  rewrite ?node_51272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51274 (s : N.State) (i : N.Inputs) :
  R.v51274 (state s) (inputs i) = Zmod.unsigned (N.v51274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51274 s i)) at 1.
  unfold R.v51274, N.v51274.
  rewrite ?node_10412.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51275 (s : N.State) (i : N.Inputs) :
  R.v51275 (state s) (inputs i) = Zmod.unsigned (N.v51275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51275 s i)) at 1.
  unfold R.v51275, N.v51275.
  unfold R.v6, N.v6.
  rewrite ?node_10571.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51276 (s : N.State) (i : N.Inputs) :
  R.v51276 (state s) (inputs i) = Zmod.unsigned (N.v51276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51276 s i)) at 1.
  unfold R.v51276, N.v51276.
  unfold R.v6, N.v6.
  rewrite ?node_10588.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51277 (s : N.State) (i : N.Inputs) :
  R.v51277 (state s) (inputs i) = Zmod.unsigned (N.v51277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51277 s i)) at 1.
  unfold R.v51277, N.v51277.
  rewrite ?node_51274.
  rewrite ?node_51275.
  rewrite ?node_51276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51278 (s : N.State) (i : N.Inputs) :
  R.v51278 (state s) (inputs i) = Zmod.unsigned (N.v51278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51278 s i)) at 1.
  unfold R.v51278, N.v51278.
  rewrite ?node_51273.
  rewrite ?node_51277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51279 (s : N.State) (i : N.Inputs) :
  R.v51279 (state s) (inputs i) = Zmod.unsigned (N.v51279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51279 s i)) at 1.
  unfold R.v51279, N.v51279.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51280 (s : N.State) (i : N.Inputs) :
  R.v51280 (state s) (inputs i) = Zmod.unsigned (N.v51280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51280 s i)) at 1.
  unfold R.v51280, N.v51280.
  rewrite ?node_10403.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51281 (s : N.State) (i : N.Inputs) :
  R.v51281 (state s) (inputs i) = Zmod.unsigned (N.v51281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51281 s i)) at 1.
  unfold R.v51281, N.v51281.
  unfold R.v6, N.v6.
  rewrite ?node_10399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51282 (s : N.State) (i : N.Inputs) :
  R.v51282 (state s) (inputs i) = Zmod.unsigned (N.v51282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51282 s i)) at 1.
  unfold R.v51282, N.v51282.
  unfold R.v6, N.v6.
  rewrite ?node_10396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51283 (s : N.State) (i : N.Inputs) :
  R.v51283 (state s) (inputs i) = Zmod.unsigned (N.v51283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51283 s i)) at 1.
  unfold R.v51283, N.v51283.
  rewrite ?node_51281.
  rewrite ?node_51282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51284 (s : N.State) (i : N.Inputs) :
  R.v51284 (state s) (inputs i) = Zmod.unsigned (N.v51284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51284 s i)) at 1.
  unfold R.v51284, N.v51284.
  unfold R.v16484, N.v16484.
  rewrite ?node_51283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51285 (s : N.State) (i : N.Inputs) :
  R.v51285 (state s) (inputs i) = Zmod.unsigned (N.v51285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51285 s i)) at 1.
  unfold R.v51285, N.v51285.
  rewrite ?node_51280.
  rewrite ?node_51284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51286 (s : N.State) (i : N.Inputs) :
  R.v51286 (state s) (inputs i) = Zmod.unsigned (N.v51286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51286 s i)) at 1.
  unfold R.v51286, N.v51286.
  unfold R.v6, N.v6.
  rewrite ?node_51285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51287 (s : N.State) (i : N.Inputs) :
  R.v51287 (state s) (inputs i) = Zmod.unsigned (N.v51287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51287 s i)) at 1.
  unfold R.v51287, N.v51287.
  rewrite ?node_10404.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51288 (s : N.State) (i : N.Inputs) :
  R.v51288 (state s) (inputs i) = Zmod.unsigned (N.v51288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51288 s i)) at 1.
  unfold R.v51288, N.v51288.
  unfold R.v6, N.v6.
  rewrite ?node_10571.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51289 (s : N.State) (i : N.Inputs) :
  R.v51289 (state s) (inputs i) = Zmod.unsigned (N.v51289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51289 s i)) at 1.
  unfold R.v51289, N.v51289.
  rewrite ?node_51287.
  rewrite ?node_51288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51290 (s : N.State) (i : N.Inputs) :
  R.v51290 (state s) (inputs i) = Zmod.unsigned (N.v51290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51290 s i)) at 1.
  unfold R.v51290, N.v51290.
  rewrite ?node_51286.
  rewrite ?node_51289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51291 (s : N.State) (i : N.Inputs) :
  R.v51291 (state s) (inputs i) = Zmod.unsigned (N.v51291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51291 s i)) at 1.
  unfold R.v51291, N.v51291.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51292 (s : N.State) (i : N.Inputs) :
  R.v51292 (state s) (inputs i) = Zmod.unsigned (N.v51292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51292 s i)) at 1.
  unfold R.v51292, N.v51292.
  rewrite ?node_10411.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51293 (s : N.State) (i : N.Inputs) :
  R.v51293 (state s) (inputs i) = Zmod.unsigned (N.v51293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51293 s i)) at 1.
  unfold R.v51293, N.v51293.
  unfold R.v6, N.v6.
  rewrite ?node_10407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51294 (s : N.State) (i : N.Inputs) :
  R.v51294 (state s) (inputs i) = Zmod.unsigned (N.v51294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51294 s i)) at 1.
  unfold R.v51294, N.v51294.
  unfold R.v6, N.v6.
  rewrite ?node_10404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51295 (s : N.State) (i : N.Inputs) :
  R.v51295 (state s) (inputs i) = Zmod.unsigned (N.v51295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51295 s i)) at 1.
  unfold R.v51295, N.v51295.
  rewrite ?node_51293.
  rewrite ?node_51294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51296 (s : N.State) (i : N.Inputs) :
  R.v51296 (state s) (inputs i) = Zmod.unsigned (N.v51296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51296 s i)) at 1.
  unfold R.v51296, N.v51296.
  unfold R.v16484, N.v16484.
  rewrite ?node_51295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51297 (s : N.State) (i : N.Inputs) :
  R.v51297 (state s) (inputs i) = Zmod.unsigned (N.v51297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51297 s i)) at 1.
  unfold R.v51297, N.v51297.
  rewrite ?node_51292.
  rewrite ?node_51296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51298 (s : N.State) (i : N.Inputs) :
  R.v51298 (state s) (inputs i) = Zmod.unsigned (N.v51298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51298 s i)) at 1.
  unfold R.v51298, N.v51298.
  unfold R.v6, N.v6.
  rewrite ?node_51297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51299 (s : N.State) (i : N.Inputs) :
  R.v51299 (state s) (inputs i) = Zmod.unsigned (N.v51299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51299 s i)) at 1.
  unfold R.v51299, N.v51299.
  rewrite ?node_10412.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51300 (s : N.State) (i : N.Inputs) :
  R.v51300 (state s) (inputs i) = Zmod.unsigned (N.v51300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51300 s i)) at 1.
  unfold R.v51300, N.v51300.
  unfold R.v6, N.v6.
  rewrite ?node_10588.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51301 (s : N.State) (i : N.Inputs) :
  R.v51301 (state s) (inputs i) = Zmod.unsigned (N.v51301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51301 s i)) at 1.
  unfold R.v51301, N.v51301.
  rewrite ?node_51299.
  rewrite ?node_51300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51302 (s : N.State) (i : N.Inputs) :
  R.v51302 (state s) (inputs i) = Zmod.unsigned (N.v51302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51302 s i)) at 1.
  unfold R.v51302, N.v51302.
  rewrite ?node_51298.
  rewrite ?node_51301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51303 (s : N.State) (i : N.Inputs) :
  R.v51303 (state s) (inputs i) = Zmod.unsigned (N.v51303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51303 s i)) at 1.
  unfold R.v51303, N.v51303.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51304 (s : N.State) (i : N.Inputs) :
  R.v51304 (state s) (inputs i) = Zmod.unsigned (N.v51304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51304 s i)) at 1.
  unfold R.v51304, N.v51304.
  rewrite ?node_10550.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51305 (s : N.State) (i : N.Inputs) :
  R.v51305 (state s) (inputs i) = Zmod.unsigned (N.v51305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51305 s i)) at 1.
  unfold R.v51305, N.v51305.
  rewrite ?node_10546.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51306 (s : N.State) (i : N.Inputs) :
  R.v51306 (state s) (inputs i) = Zmod.unsigned (N.v51306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51306 s i)) at 1.
  unfold R.v51306, N.v51306.
  rewrite ?node_10526.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51307 (s : N.State) (i : N.Inputs) :
  R.v51307 (state s) (inputs i) = Zmod.unsigned (N.v51307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51307 s i)) at 1.
  unfold R.v51307, N.v51307.
  unfold R.v6, N.v6.
  rewrite ?node_10508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51308 (s : N.State) (i : N.Inputs) :
  R.v51308 (state s) (inputs i) = Zmod.unsigned (N.v51308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51308 s i)) at 1.
  unfold R.v51308, N.v51308.
  unfold R.v6, N.v6.
  rewrite ?node_10473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51309 (s : N.State) (i : N.Inputs) :
  R.v51309 (state s) (inputs i) = Zmod.unsigned (N.v51309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51309 s i)) at 1.
  unfold R.v51309, N.v51309.
  rewrite ?node_51307.
  rewrite ?node_51308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51310 (s : N.State) (i : N.Inputs) :
  R.v51310 (state s) (inputs i) = Zmod.unsigned (N.v51310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51310 s i)) at 1.
  unfold R.v51310, N.v51310.
  unfold R.v16484, N.v16484.
  rewrite ?node_51309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51311 (s : N.State) (i : N.Inputs) :
  R.v51311 (state s) (inputs i) = Zmod.unsigned (N.v51311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51311 s i)) at 1.
  unfold R.v51311, N.v51311.
  rewrite ?node_51304.
  rewrite ?node_51305.
  rewrite ?node_51306.
  rewrite ?node_51310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51312 (s : N.State) (i : N.Inputs) :
  R.v51312 (state s) (inputs i) = Zmod.unsigned (N.v51312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51312 s i)) at 1.
  unfold R.v51312, N.v51312.
  unfold R.v6, N.v6.
  rewrite ?node_51311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51313 (s : N.State) (i : N.Inputs) :
  R.v51313 (state s) (inputs i) = Zmod.unsigned (N.v51313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51313 s i)) at 1.
  unfold R.v51313, N.v51313.
  rewrite ?node_10551.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51314 (s : N.State) (i : N.Inputs) :
  R.v51314 (state s) (inputs i) = Zmod.unsigned (N.v51314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51314 s i)) at 1.
  unfold R.v51314, N.v51314.
  unfold R.v6, N.v6.
  rewrite ?node_10709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51315 (s : N.State) (i : N.Inputs) :
  R.v51315 (state s) (inputs i) = Zmod.unsigned (N.v51315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51315 s i)) at 1.
  unfold R.v51315, N.v51315.
  unfold R.v6, N.v6.
  rewrite ?node_10741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51316 (s : N.State) (i : N.Inputs) :
  R.v51316 (state s) (inputs i) = Zmod.unsigned (N.v51316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51316 s i)) at 1.
  unfold R.v51316, N.v51316.
  rewrite ?node_51313.
  rewrite ?node_51314.
  rewrite ?node_51315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51317 (s : N.State) (i : N.Inputs) :
  R.v51317 (state s) (inputs i) = Zmod.unsigned (N.v51317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51317 s i)) at 1.
  unfold R.v51317, N.v51317.
  rewrite ?node_51312.
  rewrite ?node_51316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51318 (s : N.State) (i : N.Inputs) :
  R.v51318 (state s) (inputs i) = Zmod.unsigned (N.v51318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51318 s i)) at 1.
  unfold R.v51318, N.v51318.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51319 (s : N.State) (i : N.Inputs) :
  R.v51319 (state s) (inputs i) = Zmod.unsigned (N.v51319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51319 s i)) at 1.
  unfold R.v51319, N.v51319.
  rewrite ?node_10526.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51320 (s : N.State) (i : N.Inputs) :
  R.v51320 (state s) (inputs i) = Zmod.unsigned (N.v51320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51320 s i)) at 1.
  unfold R.v51320, N.v51320.
  unfold R.v6, N.v6.
  rewrite ?node_10508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51321 (s : N.State) (i : N.Inputs) :
  R.v51321 (state s) (inputs i) = Zmod.unsigned (N.v51321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51321 s i)) at 1.
  unfold R.v51321, N.v51321.
  unfold R.v6, N.v6.
  rewrite ?node_10473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51322 (s : N.State) (i : N.Inputs) :
  R.v51322 (state s) (inputs i) = Zmod.unsigned (N.v51322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51322 s i)) at 1.
  unfold R.v51322, N.v51322.
  rewrite ?node_51320.
  rewrite ?node_51321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51323 (s : N.State) (i : N.Inputs) :
  R.v51323 (state s) (inputs i) = Zmod.unsigned (N.v51323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51323 s i)) at 1.
  unfold R.v51323, N.v51323.
  unfold R.v16484, N.v16484.
  rewrite ?node_51322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51324 (s : N.State) (i : N.Inputs) :
  R.v51324 (state s) (inputs i) = Zmod.unsigned (N.v51324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51324 s i)) at 1.
  unfold R.v51324, N.v51324.
  rewrite ?node_51319.
  rewrite ?node_51323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51325 (s : N.State) (i : N.Inputs) :
  R.v51325 (state s) (inputs i) = Zmod.unsigned (N.v51325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51325 s i)) at 1.
  unfold R.v51325, N.v51325.
  unfold R.v6, N.v6.
  rewrite ?node_51324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51326 (s : N.State) (i : N.Inputs) :
  R.v51326 (state s) (inputs i) = Zmod.unsigned (N.v51326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51326 s i)) at 1.
  unfold R.v51326, N.v51326.
  rewrite ?node_10527.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51327 (s : N.State) (i : N.Inputs) :
  R.v51327 (state s) (inputs i) = Zmod.unsigned (N.v51327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51327 s i)) at 1.
  unfold R.v51327, N.v51327.
  unfold R.v6, N.v6.
  rewrite ?node_10709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51328 (s : N.State) (i : N.Inputs) :
  R.v51328 (state s) (inputs i) = Zmod.unsigned (N.v51328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51328 s i)) at 1.
  unfold R.v51328, N.v51328.
  rewrite ?node_51326.
  rewrite ?node_51327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51329 (s : N.State) (i : N.Inputs) :
  R.v51329 (state s) (inputs i) = Zmod.unsigned (N.v51329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51329 s i)) at 1.
  unfold R.v51329, N.v51329.
  rewrite ?node_51325.
  rewrite ?node_51328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51330 (s : N.State) (i : N.Inputs) :
  R.v51330 (state s) (inputs i) = Zmod.unsigned (N.v51330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51330 s i)) at 1.
  unfold R.v51330, N.v51330.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51331 (s : N.State) (i : N.Inputs) :
  R.v51331 (state s) (inputs i) = Zmod.unsigned (N.v51331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51331 s i)) at 1.
  unfold R.v51331, N.v51331.
  rewrite ?node_10550.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51332 (s : N.State) (i : N.Inputs) :
  R.v51332 (state s) (inputs i) = Zmod.unsigned (N.v51332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51332 s i)) at 1.
  unfold R.v51332, N.v51332.
  unfold R.v6, N.v6.
  rewrite ?node_10546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51333 (s : N.State) (i : N.Inputs) :
  R.v51333 (state s) (inputs i) = Zmod.unsigned (N.v51333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51333 s i)) at 1.
  unfold R.v51333, N.v51333.
  unfold R.v6, N.v6.
  rewrite ?node_10527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51334 (s : N.State) (i : N.Inputs) :
  R.v51334 (state s) (inputs i) = Zmod.unsigned (N.v51334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51334 s i)) at 1.
  unfold R.v51334, N.v51334.
  rewrite ?node_51332.
  rewrite ?node_51333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51335 (s : N.State) (i : N.Inputs) :
  R.v51335 (state s) (inputs i) = Zmod.unsigned (N.v51335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51335 s i)) at 1.
  unfold R.v51335, N.v51335.
  unfold R.v16484, N.v16484.
  rewrite ?node_51334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51336 (s : N.State) (i : N.Inputs) :
  R.v51336 (state s) (inputs i) = Zmod.unsigned (N.v51336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51336 s i)) at 1.
  unfold R.v51336, N.v51336.
  rewrite ?node_51331.
  rewrite ?node_51335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51337 (s : N.State) (i : N.Inputs) :
  R.v51337 (state s) (inputs i) = Zmod.unsigned (N.v51337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51337 s i)) at 1.
  unfold R.v51337, N.v51337.
  unfold R.v6, N.v6.
  rewrite ?node_51336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51338 (s : N.State) (i : N.Inputs) :
  R.v51338 (state s) (inputs i) = Zmod.unsigned (N.v51338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51338 s i)) at 1.
  unfold R.v51338, N.v51338.
  rewrite ?node_10551.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51339 (s : N.State) (i : N.Inputs) :
  R.v51339 (state s) (inputs i) = Zmod.unsigned (N.v51339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51339 s i)) at 1.
  unfold R.v51339, N.v51339.
  unfold R.v6, N.v6.
  rewrite ?node_10741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51340 (s : N.State) (i : N.Inputs) :
  R.v51340 (state s) (inputs i) = Zmod.unsigned (N.v51340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51340 s i)) at 1.
  unfold R.v51340, N.v51340.
  rewrite ?node_51338.
  rewrite ?node_51339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51341 (s : N.State) (i : N.Inputs) :
  R.v51341 (state s) (inputs i) = Zmod.unsigned (N.v51341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51341 s i)) at 1.
  unfold R.v51341, N.v51341.
  rewrite ?node_51337.
  rewrite ?node_51340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51342 (s : N.State) (i : N.Inputs) :
  R.v51342 (state s) (inputs i) = Zmod.unsigned (N.v51342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51342 s i)) at 1.
  unfold R.v51342, N.v51342.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51343 (s : N.State) (i : N.Inputs) :
  R.v51343 (state s) (inputs i) = Zmod.unsigned (N.v51343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51343 s i)) at 1.
  unfold R.v51343, N.v51343.
  rewrite ?node_10571.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51344 (s : N.State) (i : N.Inputs) :
  R.v51344 (state s) (inputs i) = Zmod.unsigned (N.v51344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51344 s i)) at 1.
  unfold R.v51344, N.v51344.
  rewrite ?node_10567.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51345 (s : N.State) (i : N.Inputs) :
  R.v51345 (state s) (inputs i) = Zmod.unsigned (N.v51345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51345 s i)) at 1.
  unfold R.v51345, N.v51345.
  rewrite ?node_10563.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51346 (s : N.State) (i : N.Inputs) :
  R.v51346 (state s) (inputs i) = Zmod.unsigned (N.v51346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51346 s i)) at 1.
  unfold R.v51346, N.v51346.
  unfold R.v6, N.v6.
  rewrite ?node_10559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51347 (s : N.State) (i : N.Inputs) :
  R.v51347 (state s) (inputs i) = Zmod.unsigned (N.v51347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51347 s i)) at 1.
  unfold R.v51347, N.v51347.
  unfold R.v6, N.v6.
  rewrite ?node_10556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51348 (s : N.State) (i : N.Inputs) :
  R.v51348 (state s) (inputs i) = Zmod.unsigned (N.v51348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51348 s i)) at 1.
  unfold R.v51348, N.v51348.
  rewrite ?node_51346.
  rewrite ?node_51347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51349 (s : N.State) (i : N.Inputs) :
  R.v51349 (state s) (inputs i) = Zmod.unsigned (N.v51349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51349 s i)) at 1.
  unfold R.v51349, N.v51349.
  unfold R.v16484, N.v16484.
  rewrite ?node_51348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51350 (s : N.State) (i : N.Inputs) :
  R.v51350 (state s) (inputs i) = Zmod.unsigned (N.v51350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51350 s i)) at 1.
  unfold R.v51350, N.v51350.
  rewrite ?node_51343.
  rewrite ?node_51344.
  rewrite ?node_51345.
  rewrite ?node_51349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51351 (s : N.State) (i : N.Inputs) :
  R.v51351 (state s) (inputs i) = Zmod.unsigned (N.v51351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51351 s i)) at 1.
  unfold R.v51351, N.v51351.
  unfold R.v6, N.v6.
  rewrite ?node_51350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51352 (s : N.State) (i : N.Inputs) :
  R.v51352 (state s) (inputs i) = Zmod.unsigned (N.v51352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51352 s i)) at 1.
  unfold R.v51352, N.v51352.
  rewrite ?node_10572.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51353 (s : N.State) (i : N.Inputs) :
  R.v51353 (state s) (inputs i) = Zmod.unsigned (N.v51353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51353 s i)) at 1.
  unfold R.v51353, N.v51353.
  unfold R.v6, N.v6.
  rewrite ?node_10730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51354 (s : N.State) (i : N.Inputs) :
  R.v51354 (state s) (inputs i) = Zmod.unsigned (N.v51354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51354 s i)) at 1.
  unfold R.v51354, N.v51354.
  unfold R.v6, N.v6.
  rewrite ?node_10749.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51355 (s : N.State) (i : N.Inputs) :
  R.v51355 (state s) (inputs i) = Zmod.unsigned (N.v51355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51355 s i)) at 1.
  unfold R.v51355, N.v51355.
  rewrite ?node_51352.
  rewrite ?node_51353.
  rewrite ?node_51354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51356 (s : N.State) (i : N.Inputs) :
  R.v51356 (state s) (inputs i) = Zmod.unsigned (N.v51356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51356 s i)) at 1.
  unfold R.v51356, N.v51356.
  rewrite ?node_51351.
  rewrite ?node_51355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51357 (s : N.State) (i : N.Inputs) :
  R.v51357 (state s) (inputs i) = Zmod.unsigned (N.v51357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51357 s i)) at 1.
  unfold R.v51357, N.v51357.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51358 (s : N.State) (i : N.Inputs) :
  R.v51358 (state s) (inputs i) = Zmod.unsigned (N.v51358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51358 s i)) at 1.
  unfold R.v51358, N.v51358.
  rewrite ?node_10563.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51359 (s : N.State) (i : N.Inputs) :
  R.v51359 (state s) (inputs i) = Zmod.unsigned (N.v51359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51359 s i)) at 1.
  unfold R.v51359, N.v51359.
  unfold R.v6, N.v6.
  rewrite ?node_10559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51360 (s : N.State) (i : N.Inputs) :
  R.v51360 (state s) (inputs i) = Zmod.unsigned (N.v51360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51360 s i)) at 1.
  unfold R.v51360, N.v51360.
  unfold R.v6, N.v6.
  rewrite ?node_10556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51361 (s : N.State) (i : N.Inputs) :
  R.v51361 (state s) (inputs i) = Zmod.unsigned (N.v51361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51361 s i)) at 1.
  unfold R.v51361, N.v51361.
  rewrite ?node_51359.
  rewrite ?node_51360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51362 (s : N.State) (i : N.Inputs) :
  R.v51362 (state s) (inputs i) = Zmod.unsigned (N.v51362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51362 s i)) at 1.
  unfold R.v51362, N.v51362.
  unfold R.v16484, N.v16484.
  rewrite ?node_51361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51363 (s : N.State) (i : N.Inputs) :
  R.v51363 (state s) (inputs i) = Zmod.unsigned (N.v51363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51363 s i)) at 1.
  unfold R.v51363, N.v51363.
  rewrite ?node_51358.
  rewrite ?node_51362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51364 (s : N.State) (i : N.Inputs) :
  R.v51364 (state s) (inputs i) = Zmod.unsigned (N.v51364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51364 s i)) at 1.
  unfold R.v51364, N.v51364.
  unfold R.v6, N.v6.
  rewrite ?node_51363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51365 (s : N.State) (i : N.Inputs) :
  R.v51365 (state s) (inputs i) = Zmod.unsigned (N.v51365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51365 s i)) at 1.
  unfold R.v51365, N.v51365.
  rewrite ?node_10564.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51366 (s : N.State) (i : N.Inputs) :
  R.v51366 (state s) (inputs i) = Zmod.unsigned (N.v51366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51366 s i)) at 1.
  unfold R.v51366, N.v51366.
  unfold R.v6, N.v6.
  rewrite ?node_10730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51367 (s : N.State) (i : N.Inputs) :
  R.v51367 (state s) (inputs i) = Zmod.unsigned (N.v51367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51367 s i)) at 1.
  unfold R.v51367, N.v51367.
  rewrite ?node_51365.
  rewrite ?node_51366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51368 (s : N.State) (i : N.Inputs) :
  R.v51368 (state s) (inputs i) = Zmod.unsigned (N.v51368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51368 s i)) at 1.
  unfold R.v51368, N.v51368.
  rewrite ?node_51364.
  rewrite ?node_51367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51369 (s : N.State) (i : N.Inputs) :
  R.v51369 (state s) (inputs i) = Zmod.unsigned (N.v51369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51369 s i)) at 1.
  unfold R.v51369, N.v51369.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51370 (s : N.State) (i : N.Inputs) :
  R.v51370 (state s) (inputs i) = Zmod.unsigned (N.v51370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51370 s i)) at 1.
  unfold R.v51370, N.v51370.
  rewrite ?node_10571.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51371 (s : N.State) (i : N.Inputs) :
  R.v51371 (state s) (inputs i) = Zmod.unsigned (N.v51371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51371 s i)) at 1.
  unfold R.v51371, N.v51371.
  unfold R.v6, N.v6.
  rewrite ?node_10567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51372 (s : N.State) (i : N.Inputs) :
  R.v51372 (state s) (inputs i) = Zmod.unsigned (N.v51372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51372 s i)) at 1.
  unfold R.v51372, N.v51372.
  unfold R.v6, N.v6.
  rewrite ?node_10564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51373 (s : N.State) (i : N.Inputs) :
  R.v51373 (state s) (inputs i) = Zmod.unsigned (N.v51373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51373 s i)) at 1.
  unfold R.v51373, N.v51373.
  rewrite ?node_51371.
  rewrite ?node_51372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51374 (s : N.State) (i : N.Inputs) :
  R.v51374 (state s) (inputs i) = Zmod.unsigned (N.v51374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51374 s i)) at 1.
  unfold R.v51374, N.v51374.
  unfold R.v16484, N.v16484.
  rewrite ?node_51373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51375 (s : N.State) (i : N.Inputs) :
  R.v51375 (state s) (inputs i) = Zmod.unsigned (N.v51375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51375 s i)) at 1.
  unfold R.v51375, N.v51375.
  rewrite ?node_51370.
  rewrite ?node_51374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51376 (s : N.State) (i : N.Inputs) :
  R.v51376 (state s) (inputs i) = Zmod.unsigned (N.v51376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51376 s i)) at 1.
  unfold R.v51376, N.v51376.
  unfold R.v6, N.v6.
  rewrite ?node_51375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51377 (s : N.State) (i : N.Inputs) :
  R.v51377 (state s) (inputs i) = Zmod.unsigned (N.v51377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51377 s i)) at 1.
  unfold R.v51377, N.v51377.
  rewrite ?node_10572.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51378 (s : N.State) (i : N.Inputs) :
  R.v51378 (state s) (inputs i) = Zmod.unsigned (N.v51378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51378 s i)) at 1.
  unfold R.v51378, N.v51378.
  unfold R.v6, N.v6.
  rewrite ?node_10749.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51379 (s : N.State) (i : N.Inputs) :
  R.v51379 (state s) (inputs i) = Zmod.unsigned (N.v51379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51379 s i)) at 1.
  unfold R.v51379, N.v51379.
  rewrite ?node_51377.
  rewrite ?node_51378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51380 (s : N.State) (i : N.Inputs) :
  R.v51380 (state s) (inputs i) = Zmod.unsigned (N.v51380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51380 s i)) at 1.
  unfold R.v51380, N.v51380.
  rewrite ?node_51376.
  rewrite ?node_51379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51381 (s : N.State) (i : N.Inputs) :
  R.v51381 (state s) (inputs i) = Zmod.unsigned (N.v51381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51381 s i)) at 1.
  unfold R.v51381, N.v51381.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51382 (s : N.State) (i : N.Inputs) :
  R.v51382 (state s) (inputs i) = Zmod.unsigned (N.v51382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51382 s i)) at 1.
  unfold R.v51382, N.v51382.
  rewrite ?node_10709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51383 (s : N.State) (i : N.Inputs) :
  R.v51383 (state s) (inputs i) = Zmod.unsigned (N.v51383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51383 s i)) at 1.
  unfold R.v51383, N.v51383.
  rewrite ?node_10705.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51384 (s : N.State) (i : N.Inputs) :
  R.v51384 (state s) (inputs i) = Zmod.unsigned (N.v51384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51384 s i)) at 1.
  unfold R.v51384, N.v51384.
  rewrite ?node_10685.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51385 (s : N.State) (i : N.Inputs) :
  R.v51385 (state s) (inputs i) = Zmod.unsigned (N.v51385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51385 s i)) at 1.
  unfold R.v51385, N.v51385.
  unfold R.v6, N.v6.
  rewrite ?node_10668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51386 (s : N.State) (i : N.Inputs) :
  R.v51386 (state s) (inputs i) = Zmod.unsigned (N.v51386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51386 s i)) at 1.
  unfold R.v51386, N.v51386.
  unfold R.v6, N.v6.
  rewrite ?node_10633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51387 (s : N.State) (i : N.Inputs) :
  R.v51387 (state s) (inputs i) = Zmod.unsigned (N.v51387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51387 s i)) at 1.
  unfold R.v51387, N.v51387.
  rewrite ?node_51385.
  rewrite ?node_51386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51388 (s : N.State) (i : N.Inputs) :
  R.v51388 (state s) (inputs i) = Zmod.unsigned (N.v51388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51388 s i)) at 1.
  unfold R.v51388, N.v51388.
  unfold R.v16484, N.v16484.
  rewrite ?node_51387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51389 (s : N.State) (i : N.Inputs) :
  R.v51389 (state s) (inputs i) = Zmod.unsigned (N.v51389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51389 s i)) at 1.
  unfold R.v51389, N.v51389.
  rewrite ?node_51382.
  rewrite ?node_51383.
  rewrite ?node_51384.
  rewrite ?node_51388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51390 (s : N.State) (i : N.Inputs) :
  R.v51390 (state s) (inputs i) = Zmod.unsigned (N.v51390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51390 s i)) at 1.
  unfold R.v51390, N.v51390.
  unfold R.v6, N.v6.
  rewrite ?node_51389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51391 (s : N.State) (i : N.Inputs) :
  R.v51391 (state s) (inputs i) = Zmod.unsigned (N.v51391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51391 s i)) at 1.
  unfold R.v51391, N.v51391.
  rewrite ?node_10710.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51392 (s : N.State) (i : N.Inputs) :
  R.v51392 (state s) (inputs i) = Zmod.unsigned (N.v51392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51392 s i)) at 1.
  unfold R.v51392, N.v51392.
  unfold R.v6, N.v6.
  rewrite ?node_10870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51393 (s : N.State) (i : N.Inputs) :
  R.v51393 (state s) (inputs i) = Zmod.unsigned (N.v51393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51393 s i)) at 1.
  unfold R.v51393, N.v51393.
  unfold R.v6, N.v6.
  rewrite ?node_10900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51394 (s : N.State) (i : N.Inputs) :
  R.v51394 (state s) (inputs i) = Zmod.unsigned (N.v51394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51394 s i)) at 1.
  unfold R.v51394, N.v51394.
  rewrite ?node_51391.
  rewrite ?node_51392.
  rewrite ?node_51393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51395 (s : N.State) (i : N.Inputs) :
  R.v51395 (state s) (inputs i) = Zmod.unsigned (N.v51395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51395 s i)) at 1.
  unfold R.v51395, N.v51395.
  rewrite ?node_51390.
  rewrite ?node_51394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51396 (s : N.State) (i : N.Inputs) :
  R.v51396 (state s) (inputs i) = Zmod.unsigned (N.v51396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51396 s i)) at 1.
  unfold R.v51396, N.v51396.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51397 (s : N.State) (i : N.Inputs) :
  R.v51397 (state s) (inputs i) = Zmod.unsigned (N.v51397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51397 s i)) at 1.
  unfold R.v51397, N.v51397.
  rewrite ?node_10685.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51398 (s : N.State) (i : N.Inputs) :
  R.v51398 (state s) (inputs i) = Zmod.unsigned (N.v51398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51398 s i)) at 1.
  unfold R.v51398, N.v51398.
  unfold R.v6, N.v6.
  rewrite ?node_10668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51399 (s : N.State) (i : N.Inputs) :
  R.v51399 (state s) (inputs i) = Zmod.unsigned (N.v51399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51399 s i)) at 1.
  unfold R.v51399, N.v51399.
  unfold R.v6, N.v6.
  rewrite ?node_10633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51400 (s : N.State) (i : N.Inputs) :
  R.v51400 (state s) (inputs i) = Zmod.unsigned (N.v51400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51400 s i)) at 1.
  unfold R.v51400, N.v51400.
  rewrite ?node_51398.
  rewrite ?node_51399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51401 (s : N.State) (i : N.Inputs) :
  R.v51401 (state s) (inputs i) = Zmod.unsigned (N.v51401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51401 s i)) at 1.
  unfold R.v51401, N.v51401.
  unfold R.v16484, N.v16484.
  rewrite ?node_51400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51402 (s : N.State) (i : N.Inputs) :
  R.v51402 (state s) (inputs i) = Zmod.unsigned (N.v51402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51402 s i)) at 1.
  unfold R.v51402, N.v51402.
  rewrite ?node_51397.
  rewrite ?node_51401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51403 (s : N.State) (i : N.Inputs) :
  R.v51403 (state s) (inputs i) = Zmod.unsigned (N.v51403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51403 s i)) at 1.
  unfold R.v51403, N.v51403.
  unfold R.v6, N.v6.
  rewrite ?node_51402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51404 (s : N.State) (i : N.Inputs) :
  R.v51404 (state s) (inputs i) = Zmod.unsigned (N.v51404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51404 s i)) at 1.
  unfold R.v51404, N.v51404.
  rewrite ?node_10686.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51405 (s : N.State) (i : N.Inputs) :
  R.v51405 (state s) (inputs i) = Zmod.unsigned (N.v51405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51405 s i)) at 1.
  unfold R.v51405, N.v51405.
  unfold R.v6, N.v6.
  rewrite ?node_10870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51406 (s : N.State) (i : N.Inputs) :
  R.v51406 (state s) (inputs i) = Zmod.unsigned (N.v51406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51406 s i)) at 1.
  unfold R.v51406, N.v51406.
  rewrite ?node_51404.
  rewrite ?node_51405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51407 (s : N.State) (i : N.Inputs) :
  R.v51407 (state s) (inputs i) = Zmod.unsigned (N.v51407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51407 s i)) at 1.
  unfold R.v51407, N.v51407.
  rewrite ?node_51403.
  rewrite ?node_51406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51408 (s : N.State) (i : N.Inputs) :
  R.v51408 (state s) (inputs i) = Zmod.unsigned (N.v51408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51408 s i)) at 1.
  unfold R.v51408, N.v51408.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51409 (s : N.State) (i : N.Inputs) :
  R.v51409 (state s) (inputs i) = Zmod.unsigned (N.v51409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51409 s i)) at 1.
  unfold R.v51409, N.v51409.
  rewrite ?node_10709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51410 (s : N.State) (i : N.Inputs) :
  R.v51410 (state s) (inputs i) = Zmod.unsigned (N.v51410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51410 s i)) at 1.
  unfold R.v51410, N.v51410.
  unfold R.v6, N.v6.
  rewrite ?node_10705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51411 (s : N.State) (i : N.Inputs) :
  R.v51411 (state s) (inputs i) = Zmod.unsigned (N.v51411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51411 s i)) at 1.
  unfold R.v51411, N.v51411.
  unfold R.v6, N.v6.
  rewrite ?node_10686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51412 (s : N.State) (i : N.Inputs) :
  R.v51412 (state s) (inputs i) = Zmod.unsigned (N.v51412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51412 s i)) at 1.
  unfold R.v51412, N.v51412.
  rewrite ?node_51410.
  rewrite ?node_51411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51413 (s : N.State) (i : N.Inputs) :
  R.v51413 (state s) (inputs i) = Zmod.unsigned (N.v51413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51413 s i)) at 1.
  unfold R.v51413, N.v51413.
  unfold R.v16484, N.v16484.
  rewrite ?node_51412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51414 (s : N.State) (i : N.Inputs) :
  R.v51414 (state s) (inputs i) = Zmod.unsigned (N.v51414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51414 s i)) at 1.
  unfold R.v51414, N.v51414.
  rewrite ?node_51409.
  rewrite ?node_51413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51415 (s : N.State) (i : N.Inputs) :
  R.v51415 (state s) (inputs i) = Zmod.unsigned (N.v51415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51415 s i)) at 1.
  unfold R.v51415, N.v51415.
  unfold R.v6, N.v6.
  rewrite ?node_51414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51416 (s : N.State) (i : N.Inputs) :
  R.v51416 (state s) (inputs i) = Zmod.unsigned (N.v51416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51416 s i)) at 1.
  unfold R.v51416, N.v51416.
  rewrite ?node_10710.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51417 (s : N.State) (i : N.Inputs) :
  R.v51417 (state s) (inputs i) = Zmod.unsigned (N.v51417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51417 s i)) at 1.
  unfold R.v51417, N.v51417.
  unfold R.v6, N.v6.
  rewrite ?node_10900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51418 (s : N.State) (i : N.Inputs) :
  R.v51418 (state s) (inputs i) = Zmod.unsigned (N.v51418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51418 s i)) at 1.
  unfold R.v51418, N.v51418.
  rewrite ?node_51416.
  rewrite ?node_51417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51419 (s : N.State) (i : N.Inputs) :
  R.v51419 (state s) (inputs i) = Zmod.unsigned (N.v51419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51419 s i)) at 1.
  unfold R.v51419, N.v51419.
  rewrite ?node_51415.
  rewrite ?node_51418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51420 (s : N.State) (i : N.Inputs) :
  R.v51420 (state s) (inputs i) = Zmod.unsigned (N.v51420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51420 s i)) at 1.
  unfold R.v51420, N.v51420.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51421 (s : N.State) (i : N.Inputs) :
  R.v51421 (state s) (inputs i) = Zmod.unsigned (N.v51421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51421 s i)) at 1.
  unfold R.v51421, N.v51421.
  rewrite ?node_10730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51422 (s : N.State) (i : N.Inputs) :
  R.v51422 (state s) (inputs i) = Zmod.unsigned (N.v51422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51422 s i)) at 1.
  unfold R.v51422, N.v51422.
  rewrite ?node_10726.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51423 (s : N.State) (i : N.Inputs) :
  R.v51423 (state s) (inputs i) = Zmod.unsigned (N.v51423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51423 s i)) at 1.
  unfold R.v51423, N.v51423.
  rewrite ?node_10722.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51424 (s : N.State) (i : N.Inputs) :
  R.v51424 (state s) (inputs i) = Zmod.unsigned (N.v51424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51424 s i)) at 1.
  unfold R.v51424, N.v51424.
  unfold R.v6, N.v6.
  rewrite ?node_10718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51425 (s : N.State) (i : N.Inputs) :
  R.v51425 (state s) (inputs i) = Zmod.unsigned (N.v51425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51425 s i)) at 1.
  unfold R.v51425, N.v51425.
  unfold R.v6, N.v6.
  rewrite ?node_10715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51426 (s : N.State) (i : N.Inputs) :
  R.v51426 (state s) (inputs i) = Zmod.unsigned (N.v51426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51426 s i)) at 1.
  unfold R.v51426, N.v51426.
  rewrite ?node_51424.
  rewrite ?node_51425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51427 (s : N.State) (i : N.Inputs) :
  R.v51427 (state s) (inputs i) = Zmod.unsigned (N.v51427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51427 s i)) at 1.
  unfold R.v51427, N.v51427.
  unfold R.v16484, N.v16484.
  rewrite ?node_51426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51428 (s : N.State) (i : N.Inputs) :
  R.v51428 (state s) (inputs i) = Zmod.unsigned (N.v51428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51428 s i)) at 1.
  unfold R.v51428, N.v51428.
  rewrite ?node_51421.
  rewrite ?node_51422.
  rewrite ?node_51423.
  rewrite ?node_51427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51429 (s : N.State) (i : N.Inputs) :
  R.v51429 (state s) (inputs i) = Zmod.unsigned (N.v51429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51429 s i)) at 1.
  unfold R.v51429, N.v51429.
  unfold R.v6, N.v6.
  rewrite ?node_51428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51430 (s : N.State) (i : N.Inputs) :
  R.v51430 (state s) (inputs i) = Zmod.unsigned (N.v51430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51430 s i)) at 1.
  unfold R.v51430, N.v51430.
  rewrite ?node_10731.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51431 (s : N.State) (i : N.Inputs) :
  R.v51431 (state s) (inputs i) = Zmod.unsigned (N.v51431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51431 s i)) at 1.
  unfold R.v51431, N.v51431.
  unfold R.v6, N.v6.
  rewrite ?node_10889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51432 (s : N.State) (i : N.Inputs) :
  R.v51432 (state s) (inputs i) = Zmod.unsigned (N.v51432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51432 s i)) at 1.
  unfold R.v51432, N.v51432.
  unfold R.v6, N.v6.
  rewrite ?node_10908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51433 (s : N.State) (i : N.Inputs) :
  R.v51433 (state s) (inputs i) = Zmod.unsigned (N.v51433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51433 s i)) at 1.
  unfold R.v51433, N.v51433.
  rewrite ?node_51430.
  rewrite ?node_51431.
  rewrite ?node_51432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51434 (s : N.State) (i : N.Inputs) :
  R.v51434 (state s) (inputs i) = Zmod.unsigned (N.v51434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51434 s i)) at 1.
  unfold R.v51434, N.v51434.
  rewrite ?node_51429.
  rewrite ?node_51433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51435 (s : N.State) (i : N.Inputs) :
  R.v51435 (state s) (inputs i) = Zmod.unsigned (N.v51435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51435 s i)) at 1.
  unfold R.v51435, N.v51435.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51436 (s : N.State) (i : N.Inputs) :
  R.v51436 (state s) (inputs i) = Zmod.unsigned (N.v51436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51436 s i)) at 1.
  unfold R.v51436, N.v51436.
  rewrite ?node_10722.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51437 (s : N.State) (i : N.Inputs) :
  R.v51437 (state s) (inputs i) = Zmod.unsigned (N.v51437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51437 s i)) at 1.
  unfold R.v51437, N.v51437.
  unfold R.v6, N.v6.
  rewrite ?node_10718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51438 (s : N.State) (i : N.Inputs) :
  R.v51438 (state s) (inputs i) = Zmod.unsigned (N.v51438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51438 s i)) at 1.
  unfold R.v51438, N.v51438.
  unfold R.v6, N.v6.
  rewrite ?node_10715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51439 (s : N.State) (i : N.Inputs) :
  R.v51439 (state s) (inputs i) = Zmod.unsigned (N.v51439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51439 s i)) at 1.
  unfold R.v51439, N.v51439.
  rewrite ?node_51437.
  rewrite ?node_51438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51440 (s : N.State) (i : N.Inputs) :
  R.v51440 (state s) (inputs i) = Zmod.unsigned (N.v51440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51440 s i)) at 1.
  unfold R.v51440, N.v51440.
  unfold R.v16484, N.v16484.
  rewrite ?node_51439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51441 (s : N.State) (i : N.Inputs) :
  R.v51441 (state s) (inputs i) = Zmod.unsigned (N.v51441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51441 s i)) at 1.
  unfold R.v51441, N.v51441.
  rewrite ?node_51436.
  rewrite ?node_51440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51442 (s : N.State) (i : N.Inputs) :
  R.v51442 (state s) (inputs i) = Zmod.unsigned (N.v51442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51442 s i)) at 1.
  unfold R.v51442, N.v51442.
  unfold R.v6, N.v6.
  rewrite ?node_51441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51443 (s : N.State) (i : N.Inputs) :
  R.v51443 (state s) (inputs i) = Zmod.unsigned (N.v51443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51443 s i)) at 1.
  unfold R.v51443, N.v51443.
  rewrite ?node_10723.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51444 (s : N.State) (i : N.Inputs) :
  R.v51444 (state s) (inputs i) = Zmod.unsigned (N.v51444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51444 s i)) at 1.
  unfold R.v51444, N.v51444.
  unfold R.v6, N.v6.
  rewrite ?node_10889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51445 (s : N.State) (i : N.Inputs) :
  R.v51445 (state s) (inputs i) = Zmod.unsigned (N.v51445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51445 s i)) at 1.
  unfold R.v51445, N.v51445.
  rewrite ?node_51443.
  rewrite ?node_51444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51446 (s : N.State) (i : N.Inputs) :
  R.v51446 (state s) (inputs i) = Zmod.unsigned (N.v51446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51446 s i)) at 1.
  unfold R.v51446, N.v51446.
  rewrite ?node_51442.
  rewrite ?node_51445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51447 (s : N.State) (i : N.Inputs) :
  R.v51447 (state s) (inputs i) = Zmod.unsigned (N.v51447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51447 s i)) at 1.
  unfold R.v51447, N.v51447.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51448 (s : N.State) (i : N.Inputs) :
  R.v51448 (state s) (inputs i) = Zmod.unsigned (N.v51448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51448 s i)) at 1.
  unfold R.v51448, N.v51448.
  rewrite ?node_10730.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51449 (s : N.State) (i : N.Inputs) :
  R.v51449 (state s) (inputs i) = Zmod.unsigned (N.v51449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51449 s i)) at 1.
  unfold R.v51449, N.v51449.
  unfold R.v6, N.v6.
  rewrite ?node_10726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51450 (s : N.State) (i : N.Inputs) :
  R.v51450 (state s) (inputs i) = Zmod.unsigned (N.v51450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51450 s i)) at 1.
  unfold R.v51450, N.v51450.
  unfold R.v6, N.v6.
  rewrite ?node_10723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51451 (s : N.State) (i : N.Inputs) :
  R.v51451 (state s) (inputs i) = Zmod.unsigned (N.v51451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51451 s i)) at 1.
  unfold R.v51451, N.v51451.
  rewrite ?node_51449.
  rewrite ?node_51450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51452 (s : N.State) (i : N.Inputs) :
  R.v51452 (state s) (inputs i) = Zmod.unsigned (N.v51452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51452 s i)) at 1.
  unfold R.v51452, N.v51452.
  unfold R.v16484, N.v16484.
  rewrite ?node_51451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51453 (s : N.State) (i : N.Inputs) :
  R.v51453 (state s) (inputs i) = Zmod.unsigned (N.v51453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51453 s i)) at 1.
  unfold R.v51453, N.v51453.
  rewrite ?node_51448.
  rewrite ?node_51452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51454 (s : N.State) (i : N.Inputs) :
  R.v51454 (state s) (inputs i) = Zmod.unsigned (N.v51454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51454 s i)) at 1.
  unfold R.v51454, N.v51454.
  unfold R.v6, N.v6.
  rewrite ?node_51453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51455 (s : N.State) (i : N.Inputs) :
  R.v51455 (state s) (inputs i) = Zmod.unsigned (N.v51455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51455 s i)) at 1.
  unfold R.v51455, N.v51455.
  rewrite ?node_10731.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51456 (s : N.State) (i : N.Inputs) :
  R.v51456 (state s) (inputs i) = Zmod.unsigned (N.v51456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51456 s i)) at 1.
  unfold R.v51456, N.v51456.
  unfold R.v6, N.v6.
  rewrite ?node_10908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51457 (s : N.State) (i : N.Inputs) :
  R.v51457 (state s) (inputs i) = Zmod.unsigned (N.v51457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51457 s i)) at 1.
  unfold R.v51457, N.v51457.
  rewrite ?node_51455.
  rewrite ?node_51456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51458 (s : N.State) (i : N.Inputs) :
  R.v51458 (state s) (inputs i) = Zmod.unsigned (N.v51458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51458 s i)) at 1.
  unfold R.v51458, N.v51458.
  rewrite ?node_51454.
  rewrite ?node_51457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51459 (s : N.State) (i : N.Inputs) :
  R.v51459 (state s) (inputs i) = Zmod.unsigned (N.v51459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51459 s i)) at 1.
  unfold R.v51459, N.v51459.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51460 (s : N.State) (i : N.Inputs) :
  R.v51460 (state s) (inputs i) = Zmod.unsigned (N.v51460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51460 s i)) at 1.
  unfold R.v51460, N.v51460.
  unfold R.v6, N.v6.
  rewrite ?node_10736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51461 (s : N.State) (i : N.Inputs) :
  R.v51461 (state s) (inputs i) = Zmod.unsigned (N.v51461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51461 s i)) at 1.
  unfold R.v51461, N.v51461.
  unfold R.v6, N.v6.
  rewrite ?node_10735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51462 (s : N.State) (i : N.Inputs) :
  R.v51462 (state s) (inputs i) = Zmod.unsigned (N.v51462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51462 s i)) at 1.
  unfold R.v51462, N.v51462.
  rewrite ?node_51460.
  rewrite ?node_51461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51463 (s : N.State) (i : N.Inputs) :
  R.v51463 (state s) (inputs i) = Zmod.unsigned (N.v51463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51463 s i)) at 1.
  unfold R.v51463, N.v51463.
  unfold R.v16463, N.v16463.
  rewrite ?node_51462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51464 (s : N.State) (i : N.Inputs) :
  R.v51464 (state s) (inputs i) = Zmod.unsigned (N.v51464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51464 s i)) at 1.
  unfold R.v51464, N.v51464.
  rewrite ?node_10737.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51465 (s : N.State) (i : N.Inputs) :
  R.v51465 (state s) (inputs i) = Zmod.unsigned (N.v51465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51465 s i)) at 1.
  unfold R.v51465, N.v51465.
  unfold R.v6, N.v6.
  rewrite ?node_10909.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51466 (s : N.State) (i : N.Inputs) :
  R.v51466 (state s) (inputs i) = Zmod.unsigned (N.v51466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51466 s i)) at 1.
  unfold R.v51466, N.v51466.
  rewrite ?node_51464.
  rewrite ?node_51465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51467 (s : N.State) (i : N.Inputs) :
  R.v51467 (state s) (inputs i) = Zmod.unsigned (N.v51467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51467 s i)) at 1.
  unfold R.v51467, N.v51467.
  rewrite ?node_51463.
  rewrite ?node_51466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51468 (s : N.State) (i : N.Inputs) :
  R.v51468 (state s) (inputs i) = Zmod.unsigned (N.v51468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51468 s i)) at 1.
  unfold R.v51468, N.v51468.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51469 (s : N.State) (i : N.Inputs) :
  R.v51469 (state s) (inputs i) = Zmod.unsigned (N.v51469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51469 s i)) at 1.
  unfold R.v51469, N.v51469.
  rewrite ?node_10870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51470 (s : N.State) (i : N.Inputs) :
  R.v51470 (state s) (inputs i) = Zmod.unsigned (N.v51470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51470 s i)) at 1.
  unfold R.v51470, N.v51470.
  rewrite ?node_10866.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51471 (s : N.State) (i : N.Inputs) :
  R.v51471 (state s) (inputs i) = Zmod.unsigned (N.v51471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51471 s i)) at 1.
  unfold R.v51471, N.v51471.
  rewrite ?node_10846.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51472 (s : N.State) (i : N.Inputs) :
  R.v51472 (state s) (inputs i) = Zmod.unsigned (N.v51472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51472 s i)) at 1.
  unfold R.v51472, N.v51472.
  unfold R.v6, N.v6.
  rewrite ?node_10829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51473 (s : N.State) (i : N.Inputs) :
  R.v51473 (state s) (inputs i) = Zmod.unsigned (N.v51473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51473 s i)) at 1.
  unfold R.v51473, N.v51473.
  unfold R.v6, N.v6.
  rewrite ?node_10794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51474 (s : N.State) (i : N.Inputs) :
  R.v51474 (state s) (inputs i) = Zmod.unsigned (N.v51474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51474 s i)) at 1.
  unfold R.v51474, N.v51474.
  rewrite ?node_51472.
  rewrite ?node_51473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51475 (s : N.State) (i : N.Inputs) :
  R.v51475 (state s) (inputs i) = Zmod.unsigned (N.v51475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51475 s i)) at 1.
  unfold R.v51475, N.v51475.
  unfold R.v16484, N.v16484.
  rewrite ?node_51474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51476 (s : N.State) (i : N.Inputs) :
  R.v51476 (state s) (inputs i) = Zmod.unsigned (N.v51476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51476 s i)) at 1.
  unfold R.v51476, N.v51476.
  rewrite ?node_51469.
  rewrite ?node_51470.
  rewrite ?node_51471.
  rewrite ?node_51475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51477 (s : N.State) (i : N.Inputs) :
  R.v51477 (state s) (inputs i) = Zmod.unsigned (N.v51477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51477 s i)) at 1.
  unfold R.v51477, N.v51477.
  unfold R.v6, N.v6.
  rewrite ?node_51476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51478 (s : N.State) (i : N.Inputs) :
  R.v51478 (state s) (inputs i) = Zmod.unsigned (N.v51478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51478 s i)) at 1.
  unfold R.v51478, N.v51478.
  rewrite ?node_10871.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51479 (s : N.State) (i : N.Inputs) :
  R.v51479 (state s) (inputs i) = Zmod.unsigned (N.v51479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51479 s i)) at 1.
  unfold R.v51479, N.v51479.
  unfold R.v6, N.v6.
  rewrite ?node_11031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51480 (s : N.State) (i : N.Inputs) :
  R.v51480 (state s) (inputs i) = Zmod.unsigned (N.v51480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51480 s i)) at 1.
  unfold R.v51480, N.v51480.
  unfold R.v6, N.v6.
  rewrite ?node_11059.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51481 (s : N.State) (i : N.Inputs) :
  R.v51481 (state s) (inputs i) = Zmod.unsigned (N.v51481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51481 s i)) at 1.
  unfold R.v51481, N.v51481.
  rewrite ?node_51478.
  rewrite ?node_51479.
  rewrite ?node_51480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51482 (s : N.State) (i : N.Inputs) :
  R.v51482 (state s) (inputs i) = Zmod.unsigned (N.v51482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51482 s i)) at 1.
  unfold R.v51482, N.v51482.
  rewrite ?node_51477.
  rewrite ?node_51481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51483 (s : N.State) (i : N.Inputs) :
  R.v51483 (state s) (inputs i) = Zmod.unsigned (N.v51483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51483 s i)) at 1.
  unfold R.v51483, N.v51483.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51484 (s : N.State) (i : N.Inputs) :
  R.v51484 (state s) (inputs i) = Zmod.unsigned (N.v51484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51484 s i)) at 1.
  unfold R.v51484, N.v51484.
  rewrite ?node_10846.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51485 (s : N.State) (i : N.Inputs) :
  R.v51485 (state s) (inputs i) = Zmod.unsigned (N.v51485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51485 s i)) at 1.
  unfold R.v51485, N.v51485.
  unfold R.v6, N.v6.
  rewrite ?node_10829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51486 (s : N.State) (i : N.Inputs) :
  R.v51486 (state s) (inputs i) = Zmod.unsigned (N.v51486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51486 s i)) at 1.
  unfold R.v51486, N.v51486.
  unfold R.v6, N.v6.
  rewrite ?node_10794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51487 (s : N.State) (i : N.Inputs) :
  R.v51487 (state s) (inputs i) = Zmod.unsigned (N.v51487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51487 s i)) at 1.
  unfold R.v51487, N.v51487.
  rewrite ?node_51485.
  rewrite ?node_51486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51488 (s : N.State) (i : N.Inputs) :
  R.v51488 (state s) (inputs i) = Zmod.unsigned (N.v51488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51488 s i)) at 1.
  unfold R.v51488, N.v51488.
  unfold R.v16484, N.v16484.
  rewrite ?node_51487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51489 (s : N.State) (i : N.Inputs) :
  R.v51489 (state s) (inputs i) = Zmod.unsigned (N.v51489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51489 s i)) at 1.
  unfold R.v51489, N.v51489.
  rewrite ?node_51484.
  rewrite ?node_51488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51490 (s : N.State) (i : N.Inputs) :
  R.v51490 (state s) (inputs i) = Zmod.unsigned (N.v51490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51490 s i)) at 1.
  unfold R.v51490, N.v51490.
  unfold R.v6, N.v6.
  rewrite ?node_51489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51491 (s : N.State) (i : N.Inputs) :
  R.v51491 (state s) (inputs i) = Zmod.unsigned (N.v51491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51491 s i)) at 1.
  unfold R.v51491, N.v51491.
  rewrite ?node_10847.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51492 (s : N.State) (i : N.Inputs) :
  R.v51492 (state s) (inputs i) = Zmod.unsigned (N.v51492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51492 s i)) at 1.
  unfold R.v51492, N.v51492.
  unfold R.v6, N.v6.
  rewrite ?node_11031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51493 (s : N.State) (i : N.Inputs) :
  R.v51493 (state s) (inputs i) = Zmod.unsigned (N.v51493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51493 s i)) at 1.
  unfold R.v51493, N.v51493.
  rewrite ?node_51491.
  rewrite ?node_51492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51494 (s : N.State) (i : N.Inputs) :
  R.v51494 (state s) (inputs i) = Zmod.unsigned (N.v51494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51494 s i)) at 1.
  unfold R.v51494, N.v51494.
  rewrite ?node_51490.
  rewrite ?node_51493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51495 (s : N.State) (i : N.Inputs) :
  R.v51495 (state s) (inputs i) = Zmod.unsigned (N.v51495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51495 s i)) at 1.
  unfold R.v51495, N.v51495.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51496 (s : N.State) (i : N.Inputs) :
  R.v51496 (state s) (inputs i) = Zmod.unsigned (N.v51496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51496 s i)) at 1.
  unfold R.v51496, N.v51496.
  rewrite ?node_10870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51497 (s : N.State) (i : N.Inputs) :
  R.v51497 (state s) (inputs i) = Zmod.unsigned (N.v51497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51497 s i)) at 1.
  unfold R.v51497, N.v51497.
  unfold R.v6, N.v6.
  rewrite ?node_10866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51498 (s : N.State) (i : N.Inputs) :
  R.v51498 (state s) (inputs i) = Zmod.unsigned (N.v51498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51498 s i)) at 1.
  unfold R.v51498, N.v51498.
  unfold R.v6, N.v6.
  rewrite ?node_10847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51499 (s : N.State) (i : N.Inputs) :
  R.v51499 (state s) (inputs i) = Zmod.unsigned (N.v51499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51499 s i)) at 1.
  unfold R.v51499, N.v51499.
  rewrite ?node_51497.
  rewrite ?node_51498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51500 (s : N.State) (i : N.Inputs) :
  R.v51500 (state s) (inputs i) = Zmod.unsigned (N.v51500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51500 s i)) at 1.
  unfold R.v51500, N.v51500.
  unfold R.v16484, N.v16484.
  rewrite ?node_51499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51501 (s : N.State) (i : N.Inputs) :
  R.v51501 (state s) (inputs i) = Zmod.unsigned (N.v51501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51501 s i)) at 1.
  unfold R.v51501, N.v51501.
  rewrite ?node_51496.
  rewrite ?node_51500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51502 (s : N.State) (i : N.Inputs) :
  R.v51502 (state s) (inputs i) = Zmod.unsigned (N.v51502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51502 s i)) at 1.
  unfold R.v51502, N.v51502.
  unfold R.v6, N.v6.
  rewrite ?node_51501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51503 (s : N.State) (i : N.Inputs) :
  R.v51503 (state s) (inputs i) = Zmod.unsigned (N.v51503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51503 s i)) at 1.
  unfold R.v51503, N.v51503.
  rewrite ?node_10871.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51504 (s : N.State) (i : N.Inputs) :
  R.v51504 (state s) (inputs i) = Zmod.unsigned (N.v51504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51504 s i)) at 1.
  unfold R.v51504, N.v51504.
  unfold R.v6, N.v6.
  rewrite ?node_11059.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51505 (s : N.State) (i : N.Inputs) :
  R.v51505 (state s) (inputs i) = Zmod.unsigned (N.v51505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51505 s i)) at 1.
  unfold R.v51505, N.v51505.
  rewrite ?node_51503.
  rewrite ?node_51504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51506 (s : N.State) (i : N.Inputs) :
  R.v51506 (state s) (inputs i) = Zmod.unsigned (N.v51506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51506 s i)) at 1.
  unfold R.v51506, N.v51506.
  rewrite ?node_51502.
  rewrite ?node_51505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51507 (s : N.State) (i : N.Inputs) :
  R.v51507 (state s) (inputs i) = Zmod.unsigned (N.v51507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51507 s i)) at 1.
  unfold R.v51507, N.v51507.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51508 (s : N.State) (i : N.Inputs) :
  R.v51508 (state s) (inputs i) = Zmod.unsigned (N.v51508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51508 s i)) at 1.
  unfold R.v51508, N.v51508.
  rewrite ?node_10889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51509 (s : N.State) (i : N.Inputs) :
  R.v51509 (state s) (inputs i) = Zmod.unsigned (N.v51509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51509 s i)) at 1.
  unfold R.v51509, N.v51509.
  rewrite ?node_10885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51510 (s : N.State) (i : N.Inputs) :
  R.v51510 (state s) (inputs i) = Zmod.unsigned (N.v51510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51510 s i)) at 1.
  unfold R.v51510, N.v51510.
  rewrite ?node_10881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51511 (s : N.State) (i : N.Inputs) :
  R.v51511 (state s) (inputs i) = Zmod.unsigned (N.v51511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51511 s i)) at 1.
  unfold R.v51511, N.v51511.
  unfold R.v6, N.v6.
  rewrite ?node_10877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51512 (s : N.State) (i : N.Inputs) :
  R.v51512 (state s) (inputs i) = Zmod.unsigned (N.v51512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51512 s i)) at 1.
  unfold R.v51512, N.v51512.
  unfold R.v6, N.v6.
  rewrite ?node_10874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51513 (s : N.State) (i : N.Inputs) :
  R.v51513 (state s) (inputs i) = Zmod.unsigned (N.v51513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51513 s i)) at 1.
  unfold R.v51513, N.v51513.
  rewrite ?node_51511.
  rewrite ?node_51512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51514 (s : N.State) (i : N.Inputs) :
  R.v51514 (state s) (inputs i) = Zmod.unsigned (N.v51514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51514 s i)) at 1.
  unfold R.v51514, N.v51514.
  unfold R.v16484, N.v16484.
  rewrite ?node_51513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51515 (s : N.State) (i : N.Inputs) :
  R.v51515 (state s) (inputs i) = Zmod.unsigned (N.v51515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51515 s i)) at 1.
  unfold R.v51515, N.v51515.
  rewrite ?node_51508.
  rewrite ?node_51509.
  rewrite ?node_51510.
  rewrite ?node_51514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51516 (s : N.State) (i : N.Inputs) :
  R.v51516 (state s) (inputs i) = Zmod.unsigned (N.v51516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51516 s i)) at 1.
  unfold R.v51516, N.v51516.
  unfold R.v6, N.v6.
  rewrite ?node_51515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51517 (s : N.State) (i : N.Inputs) :
  R.v51517 (state s) (inputs i) = Zmod.unsigned (N.v51517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51517 s i)) at 1.
  unfold R.v51517, N.v51517.
  rewrite ?node_10890.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51518 (s : N.State) (i : N.Inputs) :
  R.v51518 (state s) (inputs i) = Zmod.unsigned (N.v51518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51518 s i)) at 1.
  unfold R.v51518, N.v51518.
  unfold R.v6, N.v6.
  rewrite ?node_11050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51519 (s : N.State) (i : N.Inputs) :
  R.v51519 (state s) (inputs i) = Zmod.unsigned (N.v51519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51519 s i)) at 1.
  unfold R.v51519, N.v51519.
  unfold R.v6, N.v6.
  rewrite ?node_11067.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51520 (s : N.State) (i : N.Inputs) :
  R.v51520 (state s) (inputs i) = Zmod.unsigned (N.v51520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51520 s i)) at 1.
  unfold R.v51520, N.v51520.
  rewrite ?node_51517.
  rewrite ?node_51518.
  rewrite ?node_51519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51521 (s : N.State) (i : N.Inputs) :
  R.v51521 (state s) (inputs i) = Zmod.unsigned (N.v51521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51521 s i)) at 1.
  unfold R.v51521, N.v51521.
  rewrite ?node_51516.
  rewrite ?node_51520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51522 (s : N.State) (i : N.Inputs) :
  R.v51522 (state s) (inputs i) = Zmod.unsigned (N.v51522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51522 s i)) at 1.
  unfold R.v51522, N.v51522.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51523 (s : N.State) (i : N.Inputs) :
  R.v51523 (state s) (inputs i) = Zmod.unsigned (N.v51523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51523 s i)) at 1.
  unfold R.v51523, N.v51523.
  rewrite ?node_10881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51524 (s : N.State) (i : N.Inputs) :
  R.v51524 (state s) (inputs i) = Zmod.unsigned (N.v51524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51524 s i)) at 1.
  unfold R.v51524, N.v51524.
  unfold R.v6, N.v6.
  rewrite ?node_10877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51525 (s : N.State) (i : N.Inputs) :
  R.v51525 (state s) (inputs i) = Zmod.unsigned (N.v51525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51525 s i)) at 1.
  unfold R.v51525, N.v51525.
  unfold R.v6, N.v6.
  rewrite ?node_10874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51526 (s : N.State) (i : N.Inputs) :
  R.v51526 (state s) (inputs i) = Zmod.unsigned (N.v51526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51526 s i)) at 1.
  unfold R.v51526, N.v51526.
  rewrite ?node_51524.
  rewrite ?node_51525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51527 (s : N.State) (i : N.Inputs) :
  R.v51527 (state s) (inputs i) = Zmod.unsigned (N.v51527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51527 s i)) at 1.
  unfold R.v51527, N.v51527.
  unfold R.v16484, N.v16484.
  rewrite ?node_51526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51528 (s : N.State) (i : N.Inputs) :
  R.v51528 (state s) (inputs i) = Zmod.unsigned (N.v51528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51528 s i)) at 1.
  unfold R.v51528, N.v51528.
  rewrite ?node_51523.
  rewrite ?node_51527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51529 (s : N.State) (i : N.Inputs) :
  R.v51529 (state s) (inputs i) = Zmod.unsigned (N.v51529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51529 s i)) at 1.
  unfold R.v51529, N.v51529.
  unfold R.v6, N.v6.
  rewrite ?node_51528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51530 (s : N.State) (i : N.Inputs) :
  R.v51530 (state s) (inputs i) = Zmod.unsigned (N.v51530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51530 s i)) at 1.
  unfold R.v51530, N.v51530.
  rewrite ?node_10882.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51531 (s : N.State) (i : N.Inputs) :
  R.v51531 (state s) (inputs i) = Zmod.unsigned (N.v51531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51531 s i)) at 1.
  unfold R.v51531, N.v51531.
  unfold R.v6, N.v6.
  rewrite ?node_11050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51532 (s : N.State) (i : N.Inputs) :
  R.v51532 (state s) (inputs i) = Zmod.unsigned (N.v51532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51532 s i)) at 1.
  unfold R.v51532, N.v51532.
  rewrite ?node_51530.
  rewrite ?node_51531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51533 (s : N.State) (i : N.Inputs) :
  R.v51533 (state s) (inputs i) = Zmod.unsigned (N.v51533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51533 s i)) at 1.
  unfold R.v51533, N.v51533.
  rewrite ?node_51529.
  rewrite ?node_51532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51534 (s : N.State) (i : N.Inputs) :
  R.v51534 (state s) (inputs i) = Zmod.unsigned (N.v51534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51534 s i)) at 1.
  unfold R.v51534, N.v51534.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51535 (s : N.State) (i : N.Inputs) :
  R.v51535 (state s) (inputs i) = Zmod.unsigned (N.v51535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51535 s i)) at 1.
  unfold R.v51535, N.v51535.
  rewrite ?node_10889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51536 (s : N.State) (i : N.Inputs) :
  R.v51536 (state s) (inputs i) = Zmod.unsigned (N.v51536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51536 s i)) at 1.
  unfold R.v51536, N.v51536.
  unfold R.v6, N.v6.
  rewrite ?node_10885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51537 (s : N.State) (i : N.Inputs) :
  R.v51537 (state s) (inputs i) = Zmod.unsigned (N.v51537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51537 s i)) at 1.
  unfold R.v51537, N.v51537.
  unfold R.v6, N.v6.
  rewrite ?node_10882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51538 (s : N.State) (i : N.Inputs) :
  R.v51538 (state s) (inputs i) = Zmod.unsigned (N.v51538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51538 s i)) at 1.
  unfold R.v51538, N.v51538.
  rewrite ?node_51536.
  rewrite ?node_51537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51539 (s : N.State) (i : N.Inputs) :
  R.v51539 (state s) (inputs i) = Zmod.unsigned (N.v51539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51539 s i)) at 1.
  unfold R.v51539, N.v51539.
  unfold R.v16484, N.v16484.
  rewrite ?node_51538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51540 (s : N.State) (i : N.Inputs) :
  R.v51540 (state s) (inputs i) = Zmod.unsigned (N.v51540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51540 s i)) at 1.
  unfold R.v51540, N.v51540.
  rewrite ?node_51535.
  rewrite ?node_51539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51541 (s : N.State) (i : N.Inputs) :
  R.v51541 (state s) (inputs i) = Zmod.unsigned (N.v51541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51541 s i)) at 1.
  unfold R.v51541, N.v51541.
  unfold R.v6, N.v6.
  rewrite ?node_51540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51542 (s : N.State) (i : N.Inputs) :
  R.v51542 (state s) (inputs i) = Zmod.unsigned (N.v51542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51542 s i)) at 1.
  unfold R.v51542, N.v51542.
  rewrite ?node_10890.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51543 (s : N.State) (i : N.Inputs) :
  R.v51543 (state s) (inputs i) = Zmod.unsigned (N.v51543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51543 s i)) at 1.
  unfold R.v51543, N.v51543.
  unfold R.v6, N.v6.
  rewrite ?node_11067.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51544 (s : N.State) (i : N.Inputs) :
  R.v51544 (state s) (inputs i) = Zmod.unsigned (N.v51544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51544 s i)) at 1.
  unfold R.v51544, N.v51544.
  rewrite ?node_51542.
  rewrite ?node_51543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51545 (s : N.State) (i : N.Inputs) :
  R.v51545 (state s) (inputs i) = Zmod.unsigned (N.v51545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51545 s i)) at 1.
  unfold R.v51545, N.v51545.
  rewrite ?node_51541.
  rewrite ?node_51544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51546 (s : N.State) (i : N.Inputs) :
  R.v51546 (state s) (inputs i) = Zmod.unsigned (N.v51546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51546 s i)) at 1.
  unfold R.v51546, N.v51546.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51547 (s : N.State) (i : N.Inputs) :
  R.v51547 (state s) (inputs i) = Zmod.unsigned (N.v51547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51547 s i)) at 1.
  unfold R.v51547, N.v51547.
  unfold R.v6, N.v6.
  rewrite ?node_10895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51548 (s : N.State) (i : N.Inputs) :
  R.v51548 (state s) (inputs i) = Zmod.unsigned (N.v51548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51548 s i)) at 1.
  unfold R.v51548, N.v51548.
  unfold R.v6, N.v6.
  rewrite ?node_10894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51549 (s : N.State) (i : N.Inputs) :
  R.v51549 (state s) (inputs i) = Zmod.unsigned (N.v51549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51549 s i)) at 1.
  unfold R.v51549, N.v51549.
  rewrite ?node_51547.
  rewrite ?node_51548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51550 (s : N.State) (i : N.Inputs) :
  R.v51550 (state s) (inputs i) = Zmod.unsigned (N.v51550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51550 s i)) at 1.
  unfold R.v51550, N.v51550.
  unfold R.v16463, N.v16463.
  rewrite ?node_51549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51551 (s : N.State) (i : N.Inputs) :
  R.v51551 (state s) (inputs i) = Zmod.unsigned (N.v51551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51551 s i)) at 1.
  unfold R.v51551, N.v51551.
  rewrite ?node_10896.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51552 (s : N.State) (i : N.Inputs) :
  R.v51552 (state s) (inputs i) = Zmod.unsigned (N.v51552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51552 s i)) at 1.
  unfold R.v51552, N.v51552.
  unfold R.v6, N.v6.
  rewrite ?node_11068.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51553 (s : N.State) (i : N.Inputs) :
  R.v51553 (state s) (inputs i) = Zmod.unsigned (N.v51553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51553 s i)) at 1.
  unfold R.v51553, N.v51553.
  rewrite ?node_51551.
  rewrite ?node_51552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51554 (s : N.State) (i : N.Inputs) :
  R.v51554 (state s) (inputs i) = Zmod.unsigned (N.v51554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51554 s i)) at 1.
  unfold R.v51554, N.v51554.
  rewrite ?node_51550.
  rewrite ?node_51553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51555 (s : N.State) (i : N.Inputs) :
  R.v51555 (state s) (inputs i) = Zmod.unsigned (N.v51555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51555 s i)) at 1.
  unfold R.v51555, N.v51555.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51556 (s : N.State) (i : N.Inputs) :
  R.v51556 (state s) (inputs i) = Zmod.unsigned (N.v51556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51556 s i)) at 1.
  unfold R.v51556, N.v51556.
  rewrite ?node_11031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51557 (s : N.State) (i : N.Inputs) :
  R.v51557 (state s) (inputs i) = Zmod.unsigned (N.v51557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51557 s i)) at 1.
  unfold R.v51557, N.v51557.
  rewrite ?node_11027.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51558 (s : N.State) (i : N.Inputs) :
  R.v51558 (state s) (inputs i) = Zmod.unsigned (N.v51558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51558 s i)) at 1.
  unfold R.v51558, N.v51558.
  rewrite ?node_11007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51559 (s : N.State) (i : N.Inputs) :
  R.v51559 (state s) (inputs i) = Zmod.unsigned (N.v51559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51559 s i)) at 1.
  unfold R.v51559, N.v51559.
  unfold R.v6, N.v6.
  rewrite ?node_10990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51560 (s : N.State) (i : N.Inputs) :
  R.v51560 (state s) (inputs i) = Zmod.unsigned (N.v51560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51560 s i)) at 1.
  unfold R.v51560, N.v51560.
  unfold R.v6, N.v6.
  rewrite ?node_10955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51561 (s : N.State) (i : N.Inputs) :
  R.v51561 (state s) (inputs i) = Zmod.unsigned (N.v51561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51561 s i)) at 1.
  unfold R.v51561, N.v51561.
  rewrite ?node_51559.
  rewrite ?node_51560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51562 (s : N.State) (i : N.Inputs) :
  R.v51562 (state s) (inputs i) = Zmod.unsigned (N.v51562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51562 s i)) at 1.
  unfold R.v51562, N.v51562.
  unfold R.v16484, N.v16484.
  rewrite ?node_51561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51563 (s : N.State) (i : N.Inputs) :
  R.v51563 (state s) (inputs i) = Zmod.unsigned (N.v51563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51563 s i)) at 1.
  unfold R.v51563, N.v51563.
  rewrite ?node_51556.
  rewrite ?node_51557.
  rewrite ?node_51558.
  rewrite ?node_51562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51564 (s : N.State) (i : N.Inputs) :
  R.v51564 (state s) (inputs i) = Zmod.unsigned (N.v51564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51564 s i)) at 1.
  unfold R.v51564, N.v51564.
  unfold R.v6, N.v6.
  rewrite ?node_51563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51565 (s : N.State) (i : N.Inputs) :
  R.v51565 (state s) (inputs i) = Zmod.unsigned (N.v51565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51565 s i)) at 1.
  unfold R.v51565, N.v51565.
  rewrite ?node_11032.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51566 (s : N.State) (i : N.Inputs) :
  R.v51566 (state s) (inputs i) = Zmod.unsigned (N.v51566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51566 s i)) at 1.
  unfold R.v51566, N.v51566.
  unfold R.v6, N.v6.
  rewrite ?node_11195.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51567 (s : N.State) (i : N.Inputs) :
  R.v51567 (state s) (inputs i) = Zmod.unsigned (N.v51567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51567 s i)) at 1.
  unfold R.v51567, N.v51567.
  unfold R.v6, N.v6.
  rewrite ?node_11219.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51568 (s : N.State) (i : N.Inputs) :
  R.v51568 (state s) (inputs i) = Zmod.unsigned (N.v51568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51568 s i)) at 1.
  unfold R.v51568, N.v51568.
  rewrite ?node_51565.
  rewrite ?node_51566.
  rewrite ?node_51567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51569 (s : N.State) (i : N.Inputs) :
  R.v51569 (state s) (inputs i) = Zmod.unsigned (N.v51569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51569 s i)) at 1.
  unfold R.v51569, N.v51569.
  rewrite ?node_51564.
  rewrite ?node_51568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51570 (s : N.State) (i : N.Inputs) :
  R.v51570 (state s) (inputs i) = Zmod.unsigned (N.v51570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51570 s i)) at 1.
  unfold R.v51570, N.v51570.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51571 (s : N.State) (i : N.Inputs) :
  R.v51571 (state s) (inputs i) = Zmod.unsigned (N.v51571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51571 s i)) at 1.
  unfold R.v51571, N.v51571.
  rewrite ?node_11007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51572 (s : N.State) (i : N.Inputs) :
  R.v51572 (state s) (inputs i) = Zmod.unsigned (N.v51572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51572 s i)) at 1.
  unfold R.v51572, N.v51572.
  unfold R.v6, N.v6.
  rewrite ?node_10990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51573 (s : N.State) (i : N.Inputs) :
  R.v51573 (state s) (inputs i) = Zmod.unsigned (N.v51573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51573 s i)) at 1.
  unfold R.v51573, N.v51573.
  unfold R.v6, N.v6.
  rewrite ?node_10955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51574 (s : N.State) (i : N.Inputs) :
  R.v51574 (state s) (inputs i) = Zmod.unsigned (N.v51574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51574 s i)) at 1.
  unfold R.v51574, N.v51574.
  rewrite ?node_51572.
  rewrite ?node_51573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51575 (s : N.State) (i : N.Inputs) :
  R.v51575 (state s) (inputs i) = Zmod.unsigned (N.v51575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51575 s i)) at 1.
  unfold R.v51575, N.v51575.
  unfold R.v16484, N.v16484.
  rewrite ?node_51574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51576 (s : N.State) (i : N.Inputs) :
  R.v51576 (state s) (inputs i) = Zmod.unsigned (N.v51576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51576 s i)) at 1.
  unfold R.v51576, N.v51576.
  rewrite ?node_51571.
  rewrite ?node_51575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51577 (s : N.State) (i : N.Inputs) :
  R.v51577 (state s) (inputs i) = Zmod.unsigned (N.v51577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51577 s i)) at 1.
  unfold R.v51577, N.v51577.
  unfold R.v6, N.v6.
  rewrite ?node_51576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51578 (s : N.State) (i : N.Inputs) :
  R.v51578 (state s) (inputs i) = Zmod.unsigned (N.v51578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51578 s i)) at 1.
  unfold R.v51578, N.v51578.
  rewrite ?node_11008.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51579 (s : N.State) (i : N.Inputs) :
  R.v51579 (state s) (inputs i) = Zmod.unsigned (N.v51579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51579 s i)) at 1.
  unfold R.v51579, N.v51579.
  unfold R.v6, N.v6.
  rewrite ?node_11195.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51580 (s : N.State) (i : N.Inputs) :
  R.v51580 (state s) (inputs i) = Zmod.unsigned (N.v51580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51580 s i)) at 1.
  unfold R.v51580, N.v51580.
  rewrite ?node_51578.
  rewrite ?node_51579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51581 (s : N.State) (i : N.Inputs) :
  R.v51581 (state s) (inputs i) = Zmod.unsigned (N.v51581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51581 s i)) at 1.
  unfold R.v51581, N.v51581.
  rewrite ?node_51577.
  rewrite ?node_51580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51582 (s : N.State) (i : N.Inputs) :
  R.v51582 (state s) (inputs i) = Zmod.unsigned (N.v51582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51582 s i)) at 1.
  unfold R.v51582, N.v51582.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51583 (s : N.State) (i : N.Inputs) :
  R.v51583 (state s) (inputs i) = Zmod.unsigned (N.v51583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51583 s i)) at 1.
  unfold R.v51583, N.v51583.
  rewrite ?node_11031.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51584 (s : N.State) (i : N.Inputs) :
  R.v51584 (state s) (inputs i) = Zmod.unsigned (N.v51584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51584 s i)) at 1.
  unfold R.v51584, N.v51584.
  unfold R.v6, N.v6.
  rewrite ?node_11027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51585 (s : N.State) (i : N.Inputs) :
  R.v51585 (state s) (inputs i) = Zmod.unsigned (N.v51585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51585 s i)) at 1.
  unfold R.v51585, N.v51585.
  unfold R.v6, N.v6.
  rewrite ?node_11008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51586 (s : N.State) (i : N.Inputs) :
  R.v51586 (state s) (inputs i) = Zmod.unsigned (N.v51586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51586 s i)) at 1.
  unfold R.v51586, N.v51586.
  rewrite ?node_51584.
  rewrite ?node_51585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51587 (s : N.State) (i : N.Inputs) :
  R.v51587 (state s) (inputs i) = Zmod.unsigned (N.v51587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51587 s i)) at 1.
  unfold R.v51587, N.v51587.
  unfold R.v16484, N.v16484.
  rewrite ?node_51586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51588 (s : N.State) (i : N.Inputs) :
  R.v51588 (state s) (inputs i) = Zmod.unsigned (N.v51588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51588 s i)) at 1.
  unfold R.v51588, N.v51588.
  rewrite ?node_51583.
  rewrite ?node_51587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51589 (s : N.State) (i : N.Inputs) :
  R.v51589 (state s) (inputs i) = Zmod.unsigned (N.v51589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51589 s i)) at 1.
  unfold R.v51589, N.v51589.
  unfold R.v6, N.v6.
  rewrite ?node_51588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51590 (s : N.State) (i : N.Inputs) :
  R.v51590 (state s) (inputs i) = Zmod.unsigned (N.v51590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51590 s i)) at 1.
  unfold R.v51590, N.v51590.
  rewrite ?node_11032.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51591 (s : N.State) (i : N.Inputs) :
  R.v51591 (state s) (inputs i) = Zmod.unsigned (N.v51591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51591 s i)) at 1.
  unfold R.v51591, N.v51591.
  unfold R.v6, N.v6.
  rewrite ?node_11219.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51592 (s : N.State) (i : N.Inputs) :
  R.v51592 (state s) (inputs i) = Zmod.unsigned (N.v51592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51592 s i)) at 1.
  unfold R.v51592, N.v51592.
  rewrite ?node_51590.
  rewrite ?node_51591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51593 (s : N.State) (i : N.Inputs) :
  R.v51593 (state s) (inputs i) = Zmod.unsigned (N.v51593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51593 s i)) at 1.
  unfold R.v51593, N.v51593.
  rewrite ?node_51589.
  rewrite ?node_51592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51594 (s : N.State) (i : N.Inputs) :
  R.v51594 (state s) (inputs i) = Zmod.unsigned (N.v51594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51594 s i)) at 1.
  unfold R.v51594, N.v51594.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51595 (s : N.State) (i : N.Inputs) :
  R.v51595 (state s) (inputs i) = Zmod.unsigned (N.v51595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51595 s i)) at 1.
  unfold R.v51595, N.v51595.
  rewrite ?node_11050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51596 (s : N.State) (i : N.Inputs) :
  R.v51596 (state s) (inputs i) = Zmod.unsigned (N.v51596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51596 s i)) at 1.
  unfold R.v51596, N.v51596.
  rewrite ?node_11046.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51597 (s : N.State) (i : N.Inputs) :
  R.v51597 (state s) (inputs i) = Zmod.unsigned (N.v51597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51597 s i)) at 1.
  unfold R.v51597, N.v51597.
  rewrite ?node_11042.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51598 (s : N.State) (i : N.Inputs) :
  R.v51598 (state s) (inputs i) = Zmod.unsigned (N.v51598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51598 s i)) at 1.
  unfold R.v51598, N.v51598.
  unfold R.v6, N.v6.
  rewrite ?node_11038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51599 (s : N.State) (i : N.Inputs) :
  R.v51599 (state s) (inputs i) = Zmod.unsigned (N.v51599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51599 s i)) at 1.
  unfold R.v51599, N.v51599.
  unfold R.v6, N.v6.
  rewrite ?node_11035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51600 (s : N.State) (i : N.Inputs) :
  R.v51600 (state s) (inputs i) = Zmod.unsigned (N.v51600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51600 s i)) at 1.
  unfold R.v51600, N.v51600.
  rewrite ?node_51598.
  rewrite ?node_51599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51601 (s : N.State) (i : N.Inputs) :
  R.v51601 (state s) (inputs i) = Zmod.unsigned (N.v51601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51601 s i)) at 1.
  unfold R.v51601, N.v51601.
  unfold R.v16484, N.v16484.
  rewrite ?node_51600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51602 (s : N.State) (i : N.Inputs) :
  R.v51602 (state s) (inputs i) = Zmod.unsigned (N.v51602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51602 s i)) at 1.
  unfold R.v51602, N.v51602.
  rewrite ?node_51595.
  rewrite ?node_51596.
  rewrite ?node_51597.
  rewrite ?node_51601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51603 (s : N.State) (i : N.Inputs) :
  R.v51603 (state s) (inputs i) = Zmod.unsigned (N.v51603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51603 s i)) at 1.
  unfold R.v51603, N.v51603.
  unfold R.v6, N.v6.
  rewrite ?node_51602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51604 (s : N.State) (i : N.Inputs) :
  R.v51604 (state s) (inputs i) = Zmod.unsigned (N.v51604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51604 s i)) at 1.
  unfold R.v51604, N.v51604.
  rewrite ?node_11051.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51605 (s : N.State) (i : N.Inputs) :
  R.v51605 (state s) (inputs i) = Zmod.unsigned (N.v51605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51605 s i)) at 1.
  unfold R.v51605, N.v51605.
  unfold R.v6, N.v6.
  rewrite ?node_11214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51606 (s : N.State) (i : N.Inputs) :
  R.v51606 (state s) (inputs i) = Zmod.unsigned (N.v51606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51606 s i)) at 1.
  unfold R.v51606, N.v51606.
  unfold R.v6, N.v6.
  rewrite ?node_11223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51607 (s : N.State) (i : N.Inputs) :
  R.v51607 (state s) (inputs i) = Zmod.unsigned (N.v51607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51607 s i)) at 1.
  unfold R.v51607, N.v51607.
  rewrite ?node_51604.
  rewrite ?node_51605.
  rewrite ?node_51606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51608 (s : N.State) (i : N.Inputs) :
  R.v51608 (state s) (inputs i) = Zmod.unsigned (N.v51608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51608 s i)) at 1.
  unfold R.v51608, N.v51608.
  rewrite ?node_51603.
  rewrite ?node_51607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51609 (s : N.State) (i : N.Inputs) :
  R.v51609 (state s) (inputs i) = Zmod.unsigned (N.v51609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51609 s i)) at 1.
  unfold R.v51609, N.v51609.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51610 (s : N.State) (i : N.Inputs) :
  R.v51610 (state s) (inputs i) = Zmod.unsigned (N.v51610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51610 s i)) at 1.
  unfold R.v51610, N.v51610.
  rewrite ?node_11042.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51611 (s : N.State) (i : N.Inputs) :
  R.v51611 (state s) (inputs i) = Zmod.unsigned (N.v51611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51611 s i)) at 1.
  unfold R.v51611, N.v51611.
  unfold R.v6, N.v6.
  rewrite ?node_11038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51612 (s : N.State) (i : N.Inputs) :
  R.v51612 (state s) (inputs i) = Zmod.unsigned (N.v51612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51612 s i)) at 1.
  unfold R.v51612, N.v51612.
  unfold R.v6, N.v6.
  rewrite ?node_11035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51613 (s : N.State) (i : N.Inputs) :
  R.v51613 (state s) (inputs i) = Zmod.unsigned (N.v51613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51613 s i)) at 1.
  unfold R.v51613, N.v51613.
  rewrite ?node_51611.
  rewrite ?node_51612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51614 (s : N.State) (i : N.Inputs) :
  R.v51614 (state s) (inputs i) = Zmod.unsigned (N.v51614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51614 s i)) at 1.
  unfold R.v51614, N.v51614.
  unfold R.v16484, N.v16484.
  rewrite ?node_51613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51615 (s : N.State) (i : N.Inputs) :
  R.v51615 (state s) (inputs i) = Zmod.unsigned (N.v51615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51615 s i)) at 1.
  unfold R.v51615, N.v51615.
  rewrite ?node_51610.
  rewrite ?node_51614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51616 (s : N.State) (i : N.Inputs) :
  R.v51616 (state s) (inputs i) = Zmod.unsigned (N.v51616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51616 s i)) at 1.
  unfold R.v51616, N.v51616.
  unfold R.v6, N.v6.
  rewrite ?node_51615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51617 (s : N.State) (i : N.Inputs) :
  R.v51617 (state s) (inputs i) = Zmod.unsigned (N.v51617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51617 s i)) at 1.
  unfold R.v51617, N.v51617.
  rewrite ?node_11043.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51618 (s : N.State) (i : N.Inputs) :
  R.v51618 (state s) (inputs i) = Zmod.unsigned (N.v51618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51618 s i)) at 1.
  unfold R.v51618, N.v51618.
  unfold R.v6, N.v6.
  rewrite ?node_11214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51619 (s : N.State) (i : N.Inputs) :
  R.v51619 (state s) (inputs i) = Zmod.unsigned (N.v51619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51619 s i)) at 1.
  unfold R.v51619, N.v51619.
  rewrite ?node_51617.
  rewrite ?node_51618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51620 (s : N.State) (i : N.Inputs) :
  R.v51620 (state s) (inputs i) = Zmod.unsigned (N.v51620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51620 s i)) at 1.
  unfold R.v51620, N.v51620.
  rewrite ?node_51616.
  rewrite ?node_51619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51621 (s : N.State) (i : N.Inputs) :
  R.v51621 (state s) (inputs i) = Zmod.unsigned (N.v51621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51621 s i)) at 1.
  unfold R.v51621, N.v51621.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51622 (s : N.State) (i : N.Inputs) :
  R.v51622 (state s) (inputs i) = Zmod.unsigned (N.v51622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51622 s i)) at 1.
  unfold R.v51622, N.v51622.
  rewrite ?node_11050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51623 (s : N.State) (i : N.Inputs) :
  R.v51623 (state s) (inputs i) = Zmod.unsigned (N.v51623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51623 s i)) at 1.
  unfold R.v51623, N.v51623.
  unfold R.v6, N.v6.
  rewrite ?node_11046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51624 (s : N.State) (i : N.Inputs) :
  R.v51624 (state s) (inputs i) = Zmod.unsigned (N.v51624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51624 s i)) at 1.
  unfold R.v51624, N.v51624.
  unfold R.v6, N.v6.
  rewrite ?node_11043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51625 (s : N.State) (i : N.Inputs) :
  R.v51625 (state s) (inputs i) = Zmod.unsigned (N.v51625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51625 s i)) at 1.
  unfold R.v51625, N.v51625.
  rewrite ?node_51623.
  rewrite ?node_51624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51626 (s : N.State) (i : N.Inputs) :
  R.v51626 (state s) (inputs i) = Zmod.unsigned (N.v51626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51626 s i)) at 1.
  unfold R.v51626, N.v51626.
  unfold R.v16484, N.v16484.
  rewrite ?node_51625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51627 (s : N.State) (i : N.Inputs) :
  R.v51627 (state s) (inputs i) = Zmod.unsigned (N.v51627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51627 s i)) at 1.
  unfold R.v51627, N.v51627.
  rewrite ?node_51622.
  rewrite ?node_51626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51628 (s : N.State) (i : N.Inputs) :
  R.v51628 (state s) (inputs i) = Zmod.unsigned (N.v51628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51628 s i)) at 1.
  unfold R.v51628, N.v51628.
  unfold R.v6, N.v6.
  rewrite ?node_51627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51629 (s : N.State) (i : N.Inputs) :
  R.v51629 (state s) (inputs i) = Zmod.unsigned (N.v51629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51629 s i)) at 1.
  unfold R.v51629, N.v51629.
  rewrite ?node_11051.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51630 (s : N.State) (i : N.Inputs) :
  R.v51630 (state s) (inputs i) = Zmod.unsigned (N.v51630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51630 s i)) at 1.
  unfold R.v51630, N.v51630.
  unfold R.v6, N.v6.
  rewrite ?node_11223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51631 (s : N.State) (i : N.Inputs) :
  R.v51631 (state s) (inputs i) = Zmod.unsigned (N.v51631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51631 s i)) at 1.
  unfold R.v51631, N.v51631.
  rewrite ?node_51629.
  rewrite ?node_51630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51632 (s : N.State) (i : N.Inputs) :
  R.v51632 (state s) (inputs i) = Zmod.unsigned (N.v51632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51632 s i)) at 1.
  unfold R.v51632, N.v51632.
  rewrite ?node_51628.
  rewrite ?node_51631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51633 (s : N.State) (i : N.Inputs) :
  R.v51633 (state s) (inputs i) = Zmod.unsigned (N.v51633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51633 s i)) at 1.
  unfold R.v51633, N.v51633.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51634 (s : N.State) (i : N.Inputs) :
  R.v51634 (state s) (inputs i) = Zmod.unsigned (N.v51634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51634 s i)) at 1.
  unfold R.v51634, N.v51634.
  rewrite ?node_11195.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51635 (s : N.State) (i : N.Inputs) :
  R.v51635 (state s) (inputs i) = Zmod.unsigned (N.v51635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51635 s i)) at 1.
  unfold R.v51635, N.v51635.
  rewrite ?node_11191.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51636 (s : N.State) (i : N.Inputs) :
  R.v51636 (state s) (inputs i) = Zmod.unsigned (N.v51636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51636 s i)) at 1.
  unfold R.v51636, N.v51636.
  rewrite ?node_11171.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51637 (s : N.State) (i : N.Inputs) :
  R.v51637 (state s) (inputs i) = Zmod.unsigned (N.v51637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51637 s i)) at 1.
  unfold R.v51637, N.v51637.
  unfold R.v6, N.v6.
  rewrite ?node_11151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51638 (s : N.State) (i : N.Inputs) :
  R.v51638 (state s) (inputs i) = Zmod.unsigned (N.v51638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51638 s i)) at 1.
  unfold R.v51638, N.v51638.
  unfold R.v6, N.v6.
  rewrite ?node_11116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51639 (s : N.State) (i : N.Inputs) :
  R.v51639 (state s) (inputs i) = Zmod.unsigned (N.v51639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51639 s i)) at 1.
  unfold R.v51639, N.v51639.
  rewrite ?node_51637.
  rewrite ?node_51638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51640 (s : N.State) (i : N.Inputs) :
  R.v51640 (state s) (inputs i) = Zmod.unsigned (N.v51640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51640 s i)) at 1.
  unfold R.v51640, N.v51640.
  unfold R.v16484, N.v16484.
  rewrite ?node_51639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51641 (s : N.State) (i : N.Inputs) :
  R.v51641 (state s) (inputs i) = Zmod.unsigned (N.v51641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51641 s i)) at 1.
  unfold R.v51641, N.v51641.
  rewrite ?node_51634.
  rewrite ?node_51635.
  rewrite ?node_51636.
  rewrite ?node_51640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51642 (s : N.State) (i : N.Inputs) :
  R.v51642 (state s) (inputs i) = Zmod.unsigned (N.v51642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51642 s i)) at 1.
  unfold R.v51642, N.v51642.
  unfold R.v6, N.v6.
  rewrite ?node_51641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51643 (s : N.State) (i : N.Inputs) :
  R.v51643 (state s) (inputs i) = Zmod.unsigned (N.v51643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51643 s i)) at 1.
  unfold R.v51643, N.v51643.
  rewrite ?node_11196.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51644 (s : N.State) (i : N.Inputs) :
  R.v51644 (state s) (inputs i) = Zmod.unsigned (N.v51644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51644 s i)) at 1.
  unfold R.v51644, N.v51644.
  unfold R.v6, N.v6.
  rewrite ?node_11349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51645 (s : N.State) (i : N.Inputs) :
  R.v51645 (state s) (inputs i) = Zmod.unsigned (N.v51645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51645 s i)) at 1.
  unfold R.v51645, N.v51645.
  unfold R.v6, N.v6.
  rewrite ?node_11377.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51646 (s : N.State) (i : N.Inputs) :
  R.v51646 (state s) (inputs i) = Zmod.unsigned (N.v51646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51646 s i)) at 1.
  unfold R.v51646, N.v51646.
  rewrite ?node_51643.
  rewrite ?node_51644.
  rewrite ?node_51645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51647 (s : N.State) (i : N.Inputs) :
  R.v51647 (state s) (inputs i) = Zmod.unsigned (N.v51647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51647 s i)) at 1.
  unfold R.v51647, N.v51647.
  rewrite ?node_51642.
  rewrite ?node_51646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51648 (s : N.State) (i : N.Inputs) :
  R.v51648 (state s) (inputs i) = Zmod.unsigned (N.v51648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51648 s i)) at 1.
  unfold R.v51648, N.v51648.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51649 (s : N.State) (i : N.Inputs) :
  R.v51649 (state s) (inputs i) = Zmod.unsigned (N.v51649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51649 s i)) at 1.
  unfold R.v51649, N.v51649.
  rewrite ?node_11171.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51650 (s : N.State) (i : N.Inputs) :
  R.v51650 (state s) (inputs i) = Zmod.unsigned (N.v51650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51650 s i)) at 1.
  unfold R.v51650, N.v51650.
  unfold R.v6, N.v6.
  rewrite ?node_11151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51651 (s : N.State) (i : N.Inputs) :
  R.v51651 (state s) (inputs i) = Zmod.unsigned (N.v51651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51651 s i)) at 1.
  unfold R.v51651, N.v51651.
  unfold R.v6, N.v6.
  rewrite ?node_11116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51652 (s : N.State) (i : N.Inputs) :
  R.v51652 (state s) (inputs i) = Zmod.unsigned (N.v51652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51652 s i)) at 1.
  unfold R.v51652, N.v51652.
  rewrite ?node_51650.
  rewrite ?node_51651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51653 (s : N.State) (i : N.Inputs) :
  R.v51653 (state s) (inputs i) = Zmod.unsigned (N.v51653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51653 s i)) at 1.
  unfold R.v51653, N.v51653.
  unfold R.v16484, N.v16484.
  rewrite ?node_51652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51654 (s : N.State) (i : N.Inputs) :
  R.v51654 (state s) (inputs i) = Zmod.unsigned (N.v51654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51654 s i)) at 1.
  unfold R.v51654, N.v51654.
  rewrite ?node_51649.
  rewrite ?node_51653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51655 (s : N.State) (i : N.Inputs) :
  R.v51655 (state s) (inputs i) = Zmod.unsigned (N.v51655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51655 s i)) at 1.
  unfold R.v51655, N.v51655.
  unfold R.v6, N.v6.
  rewrite ?node_51654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51656 (s : N.State) (i : N.Inputs) :
  R.v51656 (state s) (inputs i) = Zmod.unsigned (N.v51656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51656 s i)) at 1.
  unfold R.v51656, N.v51656.
  rewrite ?node_11172.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51657 (s : N.State) (i : N.Inputs) :
  R.v51657 (state s) (inputs i) = Zmod.unsigned (N.v51657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51657 s i)) at 1.
  unfold R.v51657, N.v51657.
  unfold R.v6, N.v6.
  rewrite ?node_11349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51658 (s : N.State) (i : N.Inputs) :
  R.v51658 (state s) (inputs i) = Zmod.unsigned (N.v51658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51658 s i)) at 1.
  unfold R.v51658, N.v51658.
  rewrite ?node_51656.
  rewrite ?node_51657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51659 (s : N.State) (i : N.Inputs) :
  R.v51659 (state s) (inputs i) = Zmod.unsigned (N.v51659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51659 s i)) at 1.
  unfold R.v51659, N.v51659.
  rewrite ?node_51655.
  rewrite ?node_51658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51660 (s : N.State) (i : N.Inputs) :
  R.v51660 (state s) (inputs i) = Zmod.unsigned (N.v51660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51660 s i)) at 1.
  unfold R.v51660, N.v51660.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51661 (s : N.State) (i : N.Inputs) :
  R.v51661 (state s) (inputs i) = Zmod.unsigned (N.v51661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51661 s i)) at 1.
  unfold R.v51661, N.v51661.
  rewrite ?node_11195.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51662 (s : N.State) (i : N.Inputs) :
  R.v51662 (state s) (inputs i) = Zmod.unsigned (N.v51662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51662 s i)) at 1.
  unfold R.v51662, N.v51662.
  unfold R.v6, N.v6.
  rewrite ?node_11191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51663 (s : N.State) (i : N.Inputs) :
  R.v51663 (state s) (inputs i) = Zmod.unsigned (N.v51663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51663 s i)) at 1.
  unfold R.v51663, N.v51663.
  unfold R.v6, N.v6.
  rewrite ?node_11172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51664 (s : N.State) (i : N.Inputs) :
  R.v51664 (state s) (inputs i) = Zmod.unsigned (N.v51664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51664 s i)) at 1.
  unfold R.v51664, N.v51664.
  rewrite ?node_51662.
  rewrite ?node_51663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51665 (s : N.State) (i : N.Inputs) :
  R.v51665 (state s) (inputs i) = Zmod.unsigned (N.v51665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51665 s i)) at 1.
  unfold R.v51665, N.v51665.
  unfold R.v16484, N.v16484.
  rewrite ?node_51664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51666 (s : N.State) (i : N.Inputs) :
  R.v51666 (state s) (inputs i) = Zmod.unsigned (N.v51666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51666 s i)) at 1.
  unfold R.v51666, N.v51666.
  rewrite ?node_51661.
  rewrite ?node_51665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51667 (s : N.State) (i : N.Inputs) :
  R.v51667 (state s) (inputs i) = Zmod.unsigned (N.v51667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51667 s i)) at 1.
  unfold R.v51667, N.v51667.
  unfold R.v6, N.v6.
  rewrite ?node_51666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51668 (s : N.State) (i : N.Inputs) :
  R.v51668 (state s) (inputs i) = Zmod.unsigned (N.v51668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51668 s i)) at 1.
  unfold R.v51668, N.v51668.
  rewrite ?node_11196.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51669 (s : N.State) (i : N.Inputs) :
  R.v51669 (state s) (inputs i) = Zmod.unsigned (N.v51669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51669 s i)) at 1.
  unfold R.v51669, N.v51669.
  unfold R.v6, N.v6.
  rewrite ?node_11377.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51670 (s : N.State) (i : N.Inputs) :
  R.v51670 (state s) (inputs i) = Zmod.unsigned (N.v51670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51670 s i)) at 1.
  unfold R.v51670, N.v51670.
  rewrite ?node_51668.
  rewrite ?node_51669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51671 (s : N.State) (i : N.Inputs) :
  R.v51671 (state s) (inputs i) = Zmod.unsigned (N.v51671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51671 s i)) at 1.
  unfold R.v51671, N.v51671.
  rewrite ?node_51667.
  rewrite ?node_51670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51672 (s : N.State) (i : N.Inputs) :
  R.v51672 (state s) (inputs i) = Zmod.unsigned (N.v51672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51672 s i)) at 1.
  unfold R.v51672, N.v51672.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51673 (s : N.State) (i : N.Inputs) :
  R.v51673 (state s) (inputs i) = Zmod.unsigned (N.v51673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51673 s i)) at 1.
  unfold R.v51673, N.v51673.
  rewrite ?node_11214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51674 (s : N.State) (i : N.Inputs) :
  R.v51674 (state s) (inputs i) = Zmod.unsigned (N.v51674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51674 s i)) at 1.
  unfold R.v51674, N.v51674.
  rewrite ?node_11210.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51675 (s : N.State) (i : N.Inputs) :
  R.v51675 (state s) (inputs i) = Zmod.unsigned (N.v51675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51675 s i)) at 1.
  unfold R.v51675, N.v51675.
  rewrite ?node_11206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51676 (s : N.State) (i : N.Inputs) :
  R.v51676 (state s) (inputs i) = Zmod.unsigned (N.v51676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51676 s i)) at 1.
  unfold R.v51676, N.v51676.
  unfold R.v6, N.v6.
  rewrite ?node_11202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51677 (s : N.State) (i : N.Inputs) :
  R.v51677 (state s) (inputs i) = Zmod.unsigned (N.v51677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51677 s i)) at 1.
  unfold R.v51677, N.v51677.
  unfold R.v6, N.v6.
  rewrite ?node_11199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51678 (s : N.State) (i : N.Inputs) :
  R.v51678 (state s) (inputs i) = Zmod.unsigned (N.v51678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51678 s i)) at 1.
  unfold R.v51678, N.v51678.
  rewrite ?node_51676.
  rewrite ?node_51677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51679 (s : N.State) (i : N.Inputs) :
  R.v51679 (state s) (inputs i) = Zmod.unsigned (N.v51679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51679 s i)) at 1.
  unfold R.v51679, N.v51679.
  unfold R.v16484, N.v16484.
  rewrite ?node_51678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51680 (s : N.State) (i : N.Inputs) :
  R.v51680 (state s) (inputs i) = Zmod.unsigned (N.v51680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51680 s i)) at 1.
  unfold R.v51680, N.v51680.
  rewrite ?node_51673.
  rewrite ?node_51674.
  rewrite ?node_51675.
  rewrite ?node_51679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51681 (s : N.State) (i : N.Inputs) :
  R.v51681 (state s) (inputs i) = Zmod.unsigned (N.v51681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51681 s i)) at 1.
  unfold R.v51681, N.v51681.
  unfold R.v6, N.v6.
  rewrite ?node_51680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51682 (s : N.State) (i : N.Inputs) :
  R.v51682 (state s) (inputs i) = Zmod.unsigned (N.v51682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51682 s i)) at 1.
  unfold R.v51682, N.v51682.
  rewrite ?node_11215.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51683 (s : N.State) (i : N.Inputs) :
  R.v51683 (state s) (inputs i) = Zmod.unsigned (N.v51683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51683 s i)) at 1.
  unfold R.v51683, N.v51683.
  unfold R.v6, N.v6.
  rewrite ?node_11368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51684 (s : N.State) (i : N.Inputs) :
  R.v51684 (state s) (inputs i) = Zmod.unsigned (N.v51684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51684 s i)) at 1.
  unfold R.v51684, N.v51684.
  unfold R.v6, N.v6.
  rewrite ?node_11385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51685 (s : N.State) (i : N.Inputs) :
  R.v51685 (state s) (inputs i) = Zmod.unsigned (N.v51685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51685 s i)) at 1.
  unfold R.v51685, N.v51685.
  rewrite ?node_51682.
  rewrite ?node_51683.
  rewrite ?node_51684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51686 (s : N.State) (i : N.Inputs) :
  R.v51686 (state s) (inputs i) = Zmod.unsigned (N.v51686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51686 s i)) at 1.
  unfold R.v51686, N.v51686.
  rewrite ?node_51681.
  rewrite ?node_51685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51687 (s : N.State) (i : N.Inputs) :
  R.v51687 (state s) (inputs i) = Zmod.unsigned (N.v51687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51687 s i)) at 1.
  unfold R.v51687, N.v51687.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51688 (s : N.State) (i : N.Inputs) :
  R.v51688 (state s) (inputs i) = Zmod.unsigned (N.v51688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51688 s i)) at 1.
  unfold R.v51688, N.v51688.
  rewrite ?node_11206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51689 (s : N.State) (i : N.Inputs) :
  R.v51689 (state s) (inputs i) = Zmod.unsigned (N.v51689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51689 s i)) at 1.
  unfold R.v51689, N.v51689.
  unfold R.v6, N.v6.
  rewrite ?node_11202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51690 (s : N.State) (i : N.Inputs) :
  R.v51690 (state s) (inputs i) = Zmod.unsigned (N.v51690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51690 s i)) at 1.
  unfold R.v51690, N.v51690.
  unfold R.v6, N.v6.
  rewrite ?node_11199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51691 (s : N.State) (i : N.Inputs) :
  R.v51691 (state s) (inputs i) = Zmod.unsigned (N.v51691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51691 s i)) at 1.
  unfold R.v51691, N.v51691.
  rewrite ?node_51689.
  rewrite ?node_51690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51692 (s : N.State) (i : N.Inputs) :
  R.v51692 (state s) (inputs i) = Zmod.unsigned (N.v51692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51692 s i)) at 1.
  unfold R.v51692, N.v51692.
  unfold R.v16484, N.v16484.
  rewrite ?node_51691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51693 (s : N.State) (i : N.Inputs) :
  R.v51693 (state s) (inputs i) = Zmod.unsigned (N.v51693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51693 s i)) at 1.
  unfold R.v51693, N.v51693.
  rewrite ?node_51688.
  rewrite ?node_51692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51694 (s : N.State) (i : N.Inputs) :
  R.v51694 (state s) (inputs i) = Zmod.unsigned (N.v51694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51694 s i)) at 1.
  unfold R.v51694, N.v51694.
  unfold R.v6, N.v6.
  rewrite ?node_51693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51695 (s : N.State) (i : N.Inputs) :
  R.v51695 (state s) (inputs i) = Zmod.unsigned (N.v51695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51695 s i)) at 1.
  unfold R.v51695, N.v51695.
  rewrite ?node_11207.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51696 (s : N.State) (i : N.Inputs) :
  R.v51696 (state s) (inputs i) = Zmod.unsigned (N.v51696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51696 s i)) at 1.
  unfold R.v51696, N.v51696.
  unfold R.v6, N.v6.
  rewrite ?node_11368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51697 (s : N.State) (i : N.Inputs) :
  R.v51697 (state s) (inputs i) = Zmod.unsigned (N.v51697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51697 s i)) at 1.
  unfold R.v51697, N.v51697.
  rewrite ?node_51695.
  rewrite ?node_51696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51698 (s : N.State) (i : N.Inputs) :
  R.v51698 (state s) (inputs i) = Zmod.unsigned (N.v51698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51698 s i)) at 1.
  unfold R.v51698, N.v51698.
  rewrite ?node_51694.
  rewrite ?node_51697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51699 (s : N.State) (i : N.Inputs) :
  R.v51699 (state s) (inputs i) = Zmod.unsigned (N.v51699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51699 s i)) at 1.
  unfold R.v51699, N.v51699.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51700 (s : N.State) (i : N.Inputs) :
  R.v51700 (state s) (inputs i) = Zmod.unsigned (N.v51700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51700 s i)) at 1.
  unfold R.v51700, N.v51700.
  rewrite ?node_11214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51701 (s : N.State) (i : N.Inputs) :
  R.v51701 (state s) (inputs i) = Zmod.unsigned (N.v51701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51701 s i)) at 1.
  unfold R.v51701, N.v51701.
  unfold R.v6, N.v6.
  rewrite ?node_11210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51702 (s : N.State) (i : N.Inputs) :
  R.v51702 (state s) (inputs i) = Zmod.unsigned (N.v51702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51702 s i)) at 1.
  unfold R.v51702, N.v51702.
  unfold R.v6, N.v6.
  rewrite ?node_11207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51703 (s : N.State) (i : N.Inputs) :
  R.v51703 (state s) (inputs i) = Zmod.unsigned (N.v51703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51703 s i)) at 1.
  unfold R.v51703, N.v51703.
  rewrite ?node_51701.
  rewrite ?node_51702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51704 (s : N.State) (i : N.Inputs) :
  R.v51704 (state s) (inputs i) = Zmod.unsigned (N.v51704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51704 s i)) at 1.
  unfold R.v51704, N.v51704.
  unfold R.v16484, N.v16484.
  rewrite ?node_51703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51705 (s : N.State) (i : N.Inputs) :
  R.v51705 (state s) (inputs i) = Zmod.unsigned (N.v51705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51705 s i)) at 1.
  unfold R.v51705, N.v51705.
  rewrite ?node_51700.
  rewrite ?node_51704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51706 (s : N.State) (i : N.Inputs) :
  R.v51706 (state s) (inputs i) = Zmod.unsigned (N.v51706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51706 s i)) at 1.
  unfold R.v51706, N.v51706.
  unfold R.v6, N.v6.
  rewrite ?node_51705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51707 (s : N.State) (i : N.Inputs) :
  R.v51707 (state s) (inputs i) = Zmod.unsigned (N.v51707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51707 s i)) at 1.
  unfold R.v51707, N.v51707.
  rewrite ?node_11215.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51708 (s : N.State) (i : N.Inputs) :
  R.v51708 (state s) (inputs i) = Zmod.unsigned (N.v51708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51708 s i)) at 1.
  unfold R.v51708, N.v51708.
  unfold R.v6, N.v6.
  rewrite ?node_11385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51709 (s : N.State) (i : N.Inputs) :
  R.v51709 (state s) (inputs i) = Zmod.unsigned (N.v51709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51709 s i)) at 1.
  unfold R.v51709, N.v51709.
  rewrite ?node_51707.
  rewrite ?node_51708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51710 (s : N.State) (i : N.Inputs) :
  R.v51710 (state s) (inputs i) = Zmod.unsigned (N.v51710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51710 s i)) at 1.
  unfold R.v51710, N.v51710.
  rewrite ?node_51706.
  rewrite ?node_51709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51711 (s : N.State) (i : N.Inputs) :
  R.v51711 (state s) (inputs i) = Zmod.unsigned (N.v51711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51711 s i)) at 1.
  unfold R.v51711, N.v51711.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51712 (s : N.State) (i : N.Inputs) :
  R.v51712 (state s) (inputs i) = Zmod.unsigned (N.v51712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51712 s i)) at 1.
  unfold R.v51712, N.v51712.
  rewrite ?node_11349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51713 (s : N.State) (i : N.Inputs) :
  R.v51713 (state s) (inputs i) = Zmod.unsigned (N.v51713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51713 s i)) at 1.
  unfold R.v51713, N.v51713.
  rewrite ?node_11345.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51714 (s : N.State) (i : N.Inputs) :
  R.v51714 (state s) (inputs i) = Zmod.unsigned (N.v51714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51714 s i)) at 1.
  unfold R.v51714, N.v51714.
  rewrite ?node_11325.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51715 (s : N.State) (i : N.Inputs) :
  R.v51715 (state s) (inputs i) = Zmod.unsigned (N.v51715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51715 s i)) at 1.
  unfold R.v51715, N.v51715.
  unfold R.v6, N.v6.
  rewrite ?node_11305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51716 (s : N.State) (i : N.Inputs) :
  R.v51716 (state s) (inputs i) = Zmod.unsigned (N.v51716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51716 s i)) at 1.
  unfold R.v51716, N.v51716.
  unfold R.v6, N.v6.
  rewrite ?node_11275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51717 (s : N.State) (i : N.Inputs) :
  R.v51717 (state s) (inputs i) = Zmod.unsigned (N.v51717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51717 s i)) at 1.
  unfold R.v51717, N.v51717.
  rewrite ?node_51715.
  rewrite ?node_51716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51718 (s : N.State) (i : N.Inputs) :
  R.v51718 (state s) (inputs i) = Zmod.unsigned (N.v51718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51718 s i)) at 1.
  unfold R.v51718, N.v51718.
  unfold R.v16484, N.v16484.
  rewrite ?node_51717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51719 (s : N.State) (i : N.Inputs) :
  R.v51719 (state s) (inputs i) = Zmod.unsigned (N.v51719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51719 s i)) at 1.
  unfold R.v51719, N.v51719.
  rewrite ?node_51712.
  rewrite ?node_51713.
  rewrite ?node_51714.
  rewrite ?node_51718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51720 (s : N.State) (i : N.Inputs) :
  R.v51720 (state s) (inputs i) = Zmod.unsigned (N.v51720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51720 s i)) at 1.
  unfold R.v51720, N.v51720.
  unfold R.v6, N.v6.
  rewrite ?node_51719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51721 (s : N.State) (i : N.Inputs) :
  R.v51721 (state s) (inputs i) = Zmod.unsigned (N.v51721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51721 s i)) at 1.
  unfold R.v51721, N.v51721.
  rewrite ?node_11350.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51722 (s : N.State) (i : N.Inputs) :
  R.v51722 (state s) (inputs i) = Zmod.unsigned (N.v51722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51722 s i)) at 1.
  unfold R.v51722, N.v51722.
  unfold R.v6, N.v6.
  rewrite ?node_11504.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51723 (s : N.State) (i : N.Inputs) :
  R.v51723 (state s) (inputs i) = Zmod.unsigned (N.v51723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51723 s i)) at 1.
  unfold R.v51723, N.v51723.
  unfold R.v6, N.v6.
  rewrite ?node_11528.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51724 (s : N.State) (i : N.Inputs) :
  R.v51724 (state s) (inputs i) = Zmod.unsigned (N.v51724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51724 s i)) at 1.
  unfold R.v51724, N.v51724.
  rewrite ?node_51721.
  rewrite ?node_51722.
  rewrite ?node_51723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51725 (s : N.State) (i : N.Inputs) :
  R.v51725 (state s) (inputs i) = Zmod.unsigned (N.v51725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51725 s i)) at 1.
  unfold R.v51725, N.v51725.
  rewrite ?node_51720.
  rewrite ?node_51724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51726 (s : N.State) (i : N.Inputs) :
  R.v51726 (state s) (inputs i) = Zmod.unsigned (N.v51726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51726 s i)) at 1.
  unfold R.v51726, N.v51726.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51727 (s : N.State) (i : N.Inputs) :
  R.v51727 (state s) (inputs i) = Zmod.unsigned (N.v51727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51727 s i)) at 1.
  unfold R.v51727, N.v51727.
  rewrite ?node_11325.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51728 (s : N.State) (i : N.Inputs) :
  R.v51728 (state s) (inputs i) = Zmod.unsigned (N.v51728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51728 s i)) at 1.
  unfold R.v51728, N.v51728.
  unfold R.v6, N.v6.
  rewrite ?node_11305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51729 (s : N.State) (i : N.Inputs) :
  R.v51729 (state s) (inputs i) = Zmod.unsigned (N.v51729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51729 s i)) at 1.
  unfold R.v51729, N.v51729.
  unfold R.v6, N.v6.
  rewrite ?node_11275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51730 (s : N.State) (i : N.Inputs) :
  R.v51730 (state s) (inputs i) = Zmod.unsigned (N.v51730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51730 s i)) at 1.
  unfold R.v51730, N.v51730.
  rewrite ?node_51728.
  rewrite ?node_51729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51731 (s : N.State) (i : N.Inputs) :
  R.v51731 (state s) (inputs i) = Zmod.unsigned (N.v51731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51731 s i)) at 1.
  unfold R.v51731, N.v51731.
  unfold R.v16484, N.v16484.
  rewrite ?node_51730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51732 (s : N.State) (i : N.Inputs) :
  R.v51732 (state s) (inputs i) = Zmod.unsigned (N.v51732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51732 s i)) at 1.
  unfold R.v51732, N.v51732.
  rewrite ?node_51727.
  rewrite ?node_51731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51733 (s : N.State) (i : N.Inputs) :
  R.v51733 (state s) (inputs i) = Zmod.unsigned (N.v51733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51733 s i)) at 1.
  unfold R.v51733, N.v51733.
  unfold R.v6, N.v6.
  rewrite ?node_51732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51734 (s : N.State) (i : N.Inputs) :
  R.v51734 (state s) (inputs i) = Zmod.unsigned (N.v51734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51734 s i)) at 1.
  unfold R.v51734, N.v51734.
  rewrite ?node_11326.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51735 (s : N.State) (i : N.Inputs) :
  R.v51735 (state s) (inputs i) = Zmod.unsigned (N.v51735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51735 s i)) at 1.
  unfold R.v51735, N.v51735.
  unfold R.v6, N.v6.
  rewrite ?node_11504.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51736 (s : N.State) (i : N.Inputs) :
  R.v51736 (state s) (inputs i) = Zmod.unsigned (N.v51736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51736 s i)) at 1.
  unfold R.v51736, N.v51736.
  rewrite ?node_51734.
  rewrite ?node_51735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51737 (s : N.State) (i : N.Inputs) :
  R.v51737 (state s) (inputs i) = Zmod.unsigned (N.v51737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51737 s i)) at 1.
  unfold R.v51737, N.v51737.
  rewrite ?node_51733.
  rewrite ?node_51736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51738 (s : N.State) (i : N.Inputs) :
  R.v51738 (state s) (inputs i) = Zmod.unsigned (N.v51738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51738 s i)) at 1.
  unfold R.v51738, N.v51738.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51739 (s : N.State) (i : N.Inputs) :
  R.v51739 (state s) (inputs i) = Zmod.unsigned (N.v51739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51739 s i)) at 1.
  unfold R.v51739, N.v51739.
  rewrite ?node_11349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51740 (s : N.State) (i : N.Inputs) :
  R.v51740 (state s) (inputs i) = Zmod.unsigned (N.v51740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51740 s i)) at 1.
  unfold R.v51740, N.v51740.
  unfold R.v6, N.v6.
  rewrite ?node_11345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51741 (s : N.State) (i : N.Inputs) :
  R.v51741 (state s) (inputs i) = Zmod.unsigned (N.v51741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51741 s i)) at 1.
  unfold R.v51741, N.v51741.
  unfold R.v6, N.v6.
  rewrite ?node_11326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51742 (s : N.State) (i : N.Inputs) :
  R.v51742 (state s) (inputs i) = Zmod.unsigned (N.v51742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51742 s i)) at 1.
  unfold R.v51742, N.v51742.
  rewrite ?node_51740.
  rewrite ?node_51741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51743 (s : N.State) (i : N.Inputs) :
  R.v51743 (state s) (inputs i) = Zmod.unsigned (N.v51743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51743 s i)) at 1.
  unfold R.v51743, N.v51743.
  unfold R.v16484, N.v16484.
  rewrite ?node_51742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51744 (s : N.State) (i : N.Inputs) :
  R.v51744 (state s) (inputs i) = Zmod.unsigned (N.v51744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51744 s i)) at 1.
  unfold R.v51744, N.v51744.
  rewrite ?node_51739.
  rewrite ?node_51743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51745 (s : N.State) (i : N.Inputs) :
  R.v51745 (state s) (inputs i) = Zmod.unsigned (N.v51745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51745 s i)) at 1.
  unfold R.v51745, N.v51745.
  unfold R.v6, N.v6.
  rewrite ?node_51744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51746 (s : N.State) (i : N.Inputs) :
  R.v51746 (state s) (inputs i) = Zmod.unsigned (N.v51746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51746 s i)) at 1.
  unfold R.v51746, N.v51746.
  rewrite ?node_11350.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51747 (s : N.State) (i : N.Inputs) :
  R.v51747 (state s) (inputs i) = Zmod.unsigned (N.v51747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51747 s i)) at 1.
  unfold R.v51747, N.v51747.
  unfold R.v6, N.v6.
  rewrite ?node_11528.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51748 (s : N.State) (i : N.Inputs) :
  R.v51748 (state s) (inputs i) = Zmod.unsigned (N.v51748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51748 s i)) at 1.
  unfold R.v51748, N.v51748.
  rewrite ?node_51746.
  rewrite ?node_51747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51749 (s : N.State) (i : N.Inputs) :
  R.v51749 (state s) (inputs i) = Zmod.unsigned (N.v51749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51749 s i)) at 1.
  unfold R.v51749, N.v51749.
  rewrite ?node_51745.
  rewrite ?node_51748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51750 (s : N.State) (i : N.Inputs) :
  R.v51750 (state s) (inputs i) = Zmod.unsigned (N.v51750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51750 s i)) at 1.
  unfold R.v51750, N.v51750.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51751 (s : N.State) (i : N.Inputs) :
  R.v51751 (state s) (inputs i) = Zmod.unsigned (N.v51751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51751 s i)) at 1.
  unfold R.v51751, N.v51751.
  rewrite ?node_11368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51752 (s : N.State) (i : N.Inputs) :
  R.v51752 (state s) (inputs i) = Zmod.unsigned (N.v51752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51752 s i)) at 1.
  unfold R.v51752, N.v51752.
  rewrite ?node_11364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51753 (s : N.State) (i : N.Inputs) :
  R.v51753 (state s) (inputs i) = Zmod.unsigned (N.v51753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51753 s i)) at 1.
  unfold R.v51753, N.v51753.
  rewrite ?node_11360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51754 (s : N.State) (i : N.Inputs) :
  R.v51754 (state s) (inputs i) = Zmod.unsigned (N.v51754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51754 s i)) at 1.
  unfold R.v51754, N.v51754.
  unfold R.v6, N.v6.
  rewrite ?node_11356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51755 (s : N.State) (i : N.Inputs) :
  R.v51755 (state s) (inputs i) = Zmod.unsigned (N.v51755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51755 s i)) at 1.
  unfold R.v51755, N.v51755.
  unfold R.v6, N.v6.
  rewrite ?node_11353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51756 (s : N.State) (i : N.Inputs) :
  R.v51756 (state s) (inputs i) = Zmod.unsigned (N.v51756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51756 s i)) at 1.
  unfold R.v51756, N.v51756.
  rewrite ?node_51754.
  rewrite ?node_51755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51757 (s : N.State) (i : N.Inputs) :
  R.v51757 (state s) (inputs i) = Zmod.unsigned (N.v51757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51757 s i)) at 1.
  unfold R.v51757, N.v51757.
  unfold R.v16484, N.v16484.
  rewrite ?node_51756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51758 (s : N.State) (i : N.Inputs) :
  R.v51758 (state s) (inputs i) = Zmod.unsigned (N.v51758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51758 s i)) at 1.
  unfold R.v51758, N.v51758.
  rewrite ?node_51751.
  rewrite ?node_51752.
  rewrite ?node_51753.
  rewrite ?node_51757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51759 (s : N.State) (i : N.Inputs) :
  R.v51759 (state s) (inputs i) = Zmod.unsigned (N.v51759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51759 s i)) at 1.
  unfold R.v51759, N.v51759.
  unfold R.v6, N.v6.
  rewrite ?node_51758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51760 (s : N.State) (i : N.Inputs) :
  R.v51760 (state s) (inputs i) = Zmod.unsigned (N.v51760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51760 s i)) at 1.
  unfold R.v51760, N.v51760.
  rewrite ?node_11369.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51761 (s : N.State) (i : N.Inputs) :
  R.v51761 (state s) (inputs i) = Zmod.unsigned (N.v51761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51761 s i)) at 1.
  unfold R.v51761, N.v51761.
  unfold R.v6, N.v6.
  rewrite ?node_11523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51762 (s : N.State) (i : N.Inputs) :
  R.v51762 (state s) (inputs i) = Zmod.unsigned (N.v51762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51762 s i)) at 1.
  unfold R.v51762, N.v51762.
  unfold R.v6, N.v6.
  rewrite ?node_11532.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51763 (s : N.State) (i : N.Inputs) :
  R.v51763 (state s) (inputs i) = Zmod.unsigned (N.v51763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51763 s i)) at 1.
  unfold R.v51763, N.v51763.
  rewrite ?node_51760.
  rewrite ?node_51761.
  rewrite ?node_51762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51764 (s : N.State) (i : N.Inputs) :
  R.v51764 (state s) (inputs i) = Zmod.unsigned (N.v51764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51764 s i)) at 1.
  unfold R.v51764, N.v51764.
  rewrite ?node_51759.
  rewrite ?node_51763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51765 (s : N.State) (i : N.Inputs) :
  R.v51765 (state s) (inputs i) = Zmod.unsigned (N.v51765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51765 s i)) at 1.
  unfold R.v51765, N.v51765.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51766 (s : N.State) (i : N.Inputs) :
  R.v51766 (state s) (inputs i) = Zmod.unsigned (N.v51766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51766 s i)) at 1.
  unfold R.v51766, N.v51766.
  rewrite ?node_11360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51767 (s : N.State) (i : N.Inputs) :
  R.v51767 (state s) (inputs i) = Zmod.unsigned (N.v51767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51767 s i)) at 1.
  unfold R.v51767, N.v51767.
  unfold R.v6, N.v6.
  rewrite ?node_11356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51768 (s : N.State) (i : N.Inputs) :
  R.v51768 (state s) (inputs i) = Zmod.unsigned (N.v51768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51768 s i)) at 1.
  unfold R.v51768, N.v51768.
  unfold R.v6, N.v6.
  rewrite ?node_11353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51769 (s : N.State) (i : N.Inputs) :
  R.v51769 (state s) (inputs i) = Zmod.unsigned (N.v51769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51769 s i)) at 1.
  unfold R.v51769, N.v51769.
  rewrite ?node_51767.
  rewrite ?node_51768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51770 (s : N.State) (i : N.Inputs) :
  R.v51770 (state s) (inputs i) = Zmod.unsigned (N.v51770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51770 s i)) at 1.
  unfold R.v51770, N.v51770.
  unfold R.v16484, N.v16484.
  rewrite ?node_51769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51771 (s : N.State) (i : N.Inputs) :
  R.v51771 (state s) (inputs i) = Zmod.unsigned (N.v51771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51771 s i)) at 1.
  unfold R.v51771, N.v51771.
  rewrite ?node_51766.
  rewrite ?node_51770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51772 (s : N.State) (i : N.Inputs) :
  R.v51772 (state s) (inputs i) = Zmod.unsigned (N.v51772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51772 s i)) at 1.
  unfold R.v51772, N.v51772.
  unfold R.v6, N.v6.
  rewrite ?node_51771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51773 (s : N.State) (i : N.Inputs) :
  R.v51773 (state s) (inputs i) = Zmod.unsigned (N.v51773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51773 s i)) at 1.
  unfold R.v51773, N.v51773.
  rewrite ?node_11361.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51774 (s : N.State) (i : N.Inputs) :
  R.v51774 (state s) (inputs i) = Zmod.unsigned (N.v51774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51774 s i)) at 1.
  unfold R.v51774, N.v51774.
  unfold R.v6, N.v6.
  rewrite ?node_11523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51775 (s : N.State) (i : N.Inputs) :
  R.v51775 (state s) (inputs i) = Zmod.unsigned (N.v51775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51775 s i)) at 1.
  unfold R.v51775, N.v51775.
  rewrite ?node_51773.
  rewrite ?node_51774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51776 (s : N.State) (i : N.Inputs) :
  R.v51776 (state s) (inputs i) = Zmod.unsigned (N.v51776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51776 s i)) at 1.
  unfold R.v51776, N.v51776.
  rewrite ?node_51772.
  rewrite ?node_51775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51777 (s : N.State) (i : N.Inputs) :
  R.v51777 (state s) (inputs i) = Zmod.unsigned (N.v51777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51777 s i)) at 1.
  unfold R.v51777, N.v51777.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51778 (s : N.State) (i : N.Inputs) :
  R.v51778 (state s) (inputs i) = Zmod.unsigned (N.v51778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51778 s i)) at 1.
  unfold R.v51778, N.v51778.
  rewrite ?node_11368.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51779 (s : N.State) (i : N.Inputs) :
  R.v51779 (state s) (inputs i) = Zmod.unsigned (N.v51779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51779 s i)) at 1.
  unfold R.v51779, N.v51779.
  unfold R.v6, N.v6.
  rewrite ?node_11364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51780 (s : N.State) (i : N.Inputs) :
  R.v51780 (state s) (inputs i) = Zmod.unsigned (N.v51780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51780 s i)) at 1.
  unfold R.v51780, N.v51780.
  unfold R.v6, N.v6.
  rewrite ?node_11361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51781 (s : N.State) (i : N.Inputs) :
  R.v51781 (state s) (inputs i) = Zmod.unsigned (N.v51781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51781 s i)) at 1.
  unfold R.v51781, N.v51781.
  rewrite ?node_51779.
  rewrite ?node_51780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51782 (s : N.State) (i : N.Inputs) :
  R.v51782 (state s) (inputs i) = Zmod.unsigned (N.v51782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51782 s i)) at 1.
  unfold R.v51782, N.v51782.
  unfold R.v16484, N.v16484.
  rewrite ?node_51781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51783 (s : N.State) (i : N.Inputs) :
  R.v51783 (state s) (inputs i) = Zmod.unsigned (N.v51783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51783 s i)) at 1.
  unfold R.v51783, N.v51783.
  rewrite ?node_51778.
  rewrite ?node_51782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51784 (s : N.State) (i : N.Inputs) :
  R.v51784 (state s) (inputs i) = Zmod.unsigned (N.v51784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51784 s i)) at 1.
  unfold R.v51784, N.v51784.
  unfold R.v6, N.v6.
  rewrite ?node_51783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51785 (s : N.State) (i : N.Inputs) :
  R.v51785 (state s) (inputs i) = Zmod.unsigned (N.v51785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51785 s i)) at 1.
  unfold R.v51785, N.v51785.
  rewrite ?node_11369.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51786 (s : N.State) (i : N.Inputs) :
  R.v51786 (state s) (inputs i) = Zmod.unsigned (N.v51786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51786 s i)) at 1.
  unfold R.v51786, N.v51786.
  unfold R.v6, N.v6.
  rewrite ?node_11532.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51787 (s : N.State) (i : N.Inputs) :
  R.v51787 (state s) (inputs i) = Zmod.unsigned (N.v51787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51787 s i)) at 1.
  unfold R.v51787, N.v51787.
  rewrite ?node_51785.
  rewrite ?node_51786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51788 (s : N.State) (i : N.Inputs) :
  R.v51788 (state s) (inputs i) = Zmod.unsigned (N.v51788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51788 s i)) at 1.
  unfold R.v51788, N.v51788.
  rewrite ?node_51784.
  rewrite ?node_51787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51789 (s : N.State) (i : N.Inputs) :
  R.v51789 (state s) (inputs i) = Zmod.unsigned (N.v51789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51789 s i)) at 1.
  unfold R.v51789, N.v51789.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51790 (s : N.State) (i : N.Inputs) :
  R.v51790 (state s) (inputs i) = Zmod.unsigned (N.v51790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51790 s i)) at 1.
  unfold R.v51790, N.v51790.
  rewrite ?node_11504.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51791 (s : N.State) (i : N.Inputs) :
  R.v51791 (state s) (inputs i) = Zmod.unsigned (N.v51791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51791 s i)) at 1.
  unfold R.v51791, N.v51791.
  rewrite ?node_11500.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51792 (s : N.State) (i : N.Inputs) :
  R.v51792 (state s) (inputs i) = Zmod.unsigned (N.v51792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51792 s i)) at 1.
  unfold R.v51792, N.v51792.
  rewrite ?node_11480.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51793 (s : N.State) (i : N.Inputs) :
  R.v51793 (state s) (inputs i) = Zmod.unsigned (N.v51793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51793 s i)) at 1.
  unfold R.v51793, N.v51793.
  unfold R.v6, N.v6.
  rewrite ?node_11460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51794 (s : N.State) (i : N.Inputs) :
  R.v51794 (state s) (inputs i) = Zmod.unsigned (N.v51794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51794 s i)) at 1.
  unfold R.v51794, N.v51794.
  unfold R.v6, N.v6.
  rewrite ?node_11430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51795 (s : N.State) (i : N.Inputs) :
  R.v51795 (state s) (inputs i) = Zmod.unsigned (N.v51795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51795 s i)) at 1.
  unfold R.v51795, N.v51795.
  rewrite ?node_51793.
  rewrite ?node_51794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51796 (s : N.State) (i : N.Inputs) :
  R.v51796 (state s) (inputs i) = Zmod.unsigned (N.v51796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51796 s i)) at 1.
  unfold R.v51796, N.v51796.
  unfold R.v16484, N.v16484.
  rewrite ?node_51795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51797 (s : N.State) (i : N.Inputs) :
  R.v51797 (state s) (inputs i) = Zmod.unsigned (N.v51797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51797 s i)) at 1.
  unfold R.v51797, N.v51797.
  rewrite ?node_51790.
  rewrite ?node_51791.
  rewrite ?node_51792.
  rewrite ?node_51796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51798 (s : N.State) (i : N.Inputs) :
  R.v51798 (state s) (inputs i) = Zmod.unsigned (N.v51798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51798 s i)) at 1.
  unfold R.v51798, N.v51798.
  unfold R.v6, N.v6.
  rewrite ?node_51797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51799 (s : N.State) (i : N.Inputs) :
  R.v51799 (state s) (inputs i) = Zmod.unsigned (N.v51799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51799 s i)) at 1.
  unfold R.v51799, N.v51799.
  rewrite ?node_11505.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51800 (s : N.State) (i : N.Inputs) :
  R.v51800 (state s) (inputs i) = Zmod.unsigned (N.v51800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51800 s i)) at 1.
  unfold R.v51800, N.v51800.
  unfold R.v6, N.v6.
  rewrite ?node_11653.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51801 (s : N.State) (i : N.Inputs) :
  R.v51801 (state s) (inputs i) = Zmod.unsigned (N.v51801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51801 s i)) at 1.
  unfold R.v51801, N.v51801.
  unfold R.v6, N.v6.
  rewrite ?node_11677.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51802 (s : N.State) (i : N.Inputs) :
  R.v51802 (state s) (inputs i) = Zmod.unsigned (N.v51802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51802 s i)) at 1.
  unfold R.v51802, N.v51802.
  rewrite ?node_51799.
  rewrite ?node_51800.
  rewrite ?node_51801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51803 (s : N.State) (i : N.Inputs) :
  R.v51803 (state s) (inputs i) = Zmod.unsigned (N.v51803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51803 s i)) at 1.
  unfold R.v51803, N.v51803.
  rewrite ?node_51798.
  rewrite ?node_51802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51804 (s : N.State) (i : N.Inputs) :
  R.v51804 (state s) (inputs i) = Zmod.unsigned (N.v51804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51804 s i)) at 1.
  unfold R.v51804, N.v51804.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51805 (s : N.State) (i : N.Inputs) :
  R.v51805 (state s) (inputs i) = Zmod.unsigned (N.v51805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51805 s i)) at 1.
  unfold R.v51805, N.v51805.
  rewrite ?node_11480.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51806 (s : N.State) (i : N.Inputs) :
  R.v51806 (state s) (inputs i) = Zmod.unsigned (N.v51806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51806 s i)) at 1.
  unfold R.v51806, N.v51806.
  unfold R.v6, N.v6.
  rewrite ?node_11460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51807 (s : N.State) (i : N.Inputs) :
  R.v51807 (state s) (inputs i) = Zmod.unsigned (N.v51807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51807 s i)) at 1.
  unfold R.v51807, N.v51807.
  unfold R.v6, N.v6.
  rewrite ?node_11430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51808 (s : N.State) (i : N.Inputs) :
  R.v51808 (state s) (inputs i) = Zmod.unsigned (N.v51808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51808 s i)) at 1.
  unfold R.v51808, N.v51808.
  rewrite ?node_51806.
  rewrite ?node_51807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51809 (s : N.State) (i : N.Inputs) :
  R.v51809 (state s) (inputs i) = Zmod.unsigned (N.v51809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51809 s i)) at 1.
  unfold R.v51809, N.v51809.
  unfold R.v16484, N.v16484.
  rewrite ?node_51808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51810 (s : N.State) (i : N.Inputs) :
  R.v51810 (state s) (inputs i) = Zmod.unsigned (N.v51810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51810 s i)) at 1.
  unfold R.v51810, N.v51810.
  rewrite ?node_51805.
  rewrite ?node_51809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51811 (s : N.State) (i : N.Inputs) :
  R.v51811 (state s) (inputs i) = Zmod.unsigned (N.v51811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51811 s i)) at 1.
  unfold R.v51811, N.v51811.
  unfold R.v6, N.v6.
  rewrite ?node_51810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51812 (s : N.State) (i : N.Inputs) :
  R.v51812 (state s) (inputs i) = Zmod.unsigned (N.v51812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51812 s i)) at 1.
  unfold R.v51812, N.v51812.
  rewrite ?node_11481.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51813 (s : N.State) (i : N.Inputs) :
  R.v51813 (state s) (inputs i) = Zmod.unsigned (N.v51813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51813 s i)) at 1.
  unfold R.v51813, N.v51813.
  unfold R.v6, N.v6.
  rewrite ?node_11653.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51814 (s : N.State) (i : N.Inputs) :
  R.v51814 (state s) (inputs i) = Zmod.unsigned (N.v51814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51814 s i)) at 1.
  unfold R.v51814, N.v51814.
  rewrite ?node_51812.
  rewrite ?node_51813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51815 (s : N.State) (i : N.Inputs) :
  R.v51815 (state s) (inputs i) = Zmod.unsigned (N.v51815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51815 s i)) at 1.
  unfold R.v51815, N.v51815.
  rewrite ?node_51811.
  rewrite ?node_51814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51816 (s : N.State) (i : N.Inputs) :
  R.v51816 (state s) (inputs i) = Zmod.unsigned (N.v51816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51816 s i)) at 1.
  unfold R.v51816, N.v51816.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51817 (s : N.State) (i : N.Inputs) :
  R.v51817 (state s) (inputs i) = Zmod.unsigned (N.v51817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51817 s i)) at 1.
  unfold R.v51817, N.v51817.
  rewrite ?node_11504.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51818 (s : N.State) (i : N.Inputs) :
  R.v51818 (state s) (inputs i) = Zmod.unsigned (N.v51818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51818 s i)) at 1.
  unfold R.v51818, N.v51818.
  unfold R.v6, N.v6.
  rewrite ?node_11500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51819 (s : N.State) (i : N.Inputs) :
  R.v51819 (state s) (inputs i) = Zmod.unsigned (N.v51819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51819 s i)) at 1.
  unfold R.v51819, N.v51819.
  unfold R.v6, N.v6.
  rewrite ?node_11481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51820 (s : N.State) (i : N.Inputs) :
  R.v51820 (state s) (inputs i) = Zmod.unsigned (N.v51820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51820 s i)) at 1.
  unfold R.v51820, N.v51820.
  rewrite ?node_51818.
  rewrite ?node_51819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51821 (s : N.State) (i : N.Inputs) :
  R.v51821 (state s) (inputs i) = Zmod.unsigned (N.v51821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51821 s i)) at 1.
  unfold R.v51821, N.v51821.
  unfold R.v16484, N.v16484.
  rewrite ?node_51820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51822 (s : N.State) (i : N.Inputs) :
  R.v51822 (state s) (inputs i) = Zmod.unsigned (N.v51822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51822 s i)) at 1.
  unfold R.v51822, N.v51822.
  rewrite ?node_51817.
  rewrite ?node_51821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51823 (s : N.State) (i : N.Inputs) :
  R.v51823 (state s) (inputs i) = Zmod.unsigned (N.v51823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51823 s i)) at 1.
  unfold R.v51823, N.v51823.
  unfold R.v6, N.v6.
  rewrite ?node_51822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51824 (s : N.State) (i : N.Inputs) :
  R.v51824 (state s) (inputs i) = Zmod.unsigned (N.v51824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51824 s i)) at 1.
  unfold R.v51824, N.v51824.
  rewrite ?node_11505.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51825 (s : N.State) (i : N.Inputs) :
  R.v51825 (state s) (inputs i) = Zmod.unsigned (N.v51825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51825 s i)) at 1.
  unfold R.v51825, N.v51825.
  unfold R.v6, N.v6.
  rewrite ?node_11677.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51826 (s : N.State) (i : N.Inputs) :
  R.v51826 (state s) (inputs i) = Zmod.unsigned (N.v51826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51826 s i)) at 1.
  unfold R.v51826, N.v51826.
  rewrite ?node_51824.
  rewrite ?node_51825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51827 (s : N.State) (i : N.Inputs) :
  R.v51827 (state s) (inputs i) = Zmod.unsigned (N.v51827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51827 s i)) at 1.
  unfold R.v51827, N.v51827.
  rewrite ?node_51823.
  rewrite ?node_51826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51828 (s : N.State) (i : N.Inputs) :
  R.v51828 (state s) (inputs i) = Zmod.unsigned (N.v51828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51828 s i)) at 1.
  unfold R.v51828, N.v51828.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51829 (s : N.State) (i : N.Inputs) :
  R.v51829 (state s) (inputs i) = Zmod.unsigned (N.v51829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51829 s i)) at 1.
  unfold R.v51829, N.v51829.
  rewrite ?node_11523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51830 (s : N.State) (i : N.Inputs) :
  R.v51830 (state s) (inputs i) = Zmod.unsigned (N.v51830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51830 s i)) at 1.
  unfold R.v51830, N.v51830.
  rewrite ?node_11519.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51831 (s : N.State) (i : N.Inputs) :
  R.v51831 (state s) (inputs i) = Zmod.unsigned (N.v51831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51831 s i)) at 1.
  unfold R.v51831, N.v51831.
  rewrite ?node_11515.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51832 (s : N.State) (i : N.Inputs) :
  R.v51832 (state s) (inputs i) = Zmod.unsigned (N.v51832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51832 s i)) at 1.
  unfold R.v51832, N.v51832.
  unfold R.v6, N.v6.
  rewrite ?node_11511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51833 (s : N.State) (i : N.Inputs) :
  R.v51833 (state s) (inputs i) = Zmod.unsigned (N.v51833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51833 s i)) at 1.
  unfold R.v51833, N.v51833.
  unfold R.v6, N.v6.
  rewrite ?node_11508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51834 (s : N.State) (i : N.Inputs) :
  R.v51834 (state s) (inputs i) = Zmod.unsigned (N.v51834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51834 s i)) at 1.
  unfold R.v51834, N.v51834.
  rewrite ?node_51832.
  rewrite ?node_51833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51835 (s : N.State) (i : N.Inputs) :
  R.v51835 (state s) (inputs i) = Zmod.unsigned (N.v51835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51835 s i)) at 1.
  unfold R.v51835, N.v51835.
  unfold R.v16484, N.v16484.
  rewrite ?node_51834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51836 (s : N.State) (i : N.Inputs) :
  R.v51836 (state s) (inputs i) = Zmod.unsigned (N.v51836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51836 s i)) at 1.
  unfold R.v51836, N.v51836.
  rewrite ?node_51829.
  rewrite ?node_51830.
  rewrite ?node_51831.
  rewrite ?node_51835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51837 (s : N.State) (i : N.Inputs) :
  R.v51837 (state s) (inputs i) = Zmod.unsigned (N.v51837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51837 s i)) at 1.
  unfold R.v51837, N.v51837.
  unfold R.v6, N.v6.
  rewrite ?node_51836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51838 (s : N.State) (i : N.Inputs) :
  R.v51838 (state s) (inputs i) = Zmod.unsigned (N.v51838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51838 s i)) at 1.
  unfold R.v51838, N.v51838.
  rewrite ?node_11524.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51839 (s : N.State) (i : N.Inputs) :
  R.v51839 (state s) (inputs i) = Zmod.unsigned (N.v51839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51839 s i)) at 1.
  unfold R.v51839, N.v51839.
  unfold R.v6, N.v6.
  rewrite ?node_11672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51840 (s : N.State) (i : N.Inputs) :
  R.v51840 (state s) (inputs i) = Zmod.unsigned (N.v51840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51840 s i)) at 1.
  unfold R.v51840, N.v51840.
  unfold R.v6, N.v6.
  rewrite ?node_11681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51841 (s : N.State) (i : N.Inputs) :
  R.v51841 (state s) (inputs i) = Zmod.unsigned (N.v51841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51841 s i)) at 1.
  unfold R.v51841, N.v51841.
  rewrite ?node_51838.
  rewrite ?node_51839.
  rewrite ?node_51840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51842 (s : N.State) (i : N.Inputs) :
  R.v51842 (state s) (inputs i) = Zmod.unsigned (N.v51842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51842 s i)) at 1.
  unfold R.v51842, N.v51842.
  rewrite ?node_51837.
  rewrite ?node_51841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51843 (s : N.State) (i : N.Inputs) :
  R.v51843 (state s) (inputs i) = Zmod.unsigned (N.v51843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51843 s i)) at 1.
  unfold R.v51843, N.v51843.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51844 (s : N.State) (i : N.Inputs) :
  R.v51844 (state s) (inputs i) = Zmod.unsigned (N.v51844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51844 s i)) at 1.
  unfold R.v51844, N.v51844.
  rewrite ?node_11515.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51845 (s : N.State) (i : N.Inputs) :
  R.v51845 (state s) (inputs i) = Zmod.unsigned (N.v51845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51845 s i)) at 1.
  unfold R.v51845, N.v51845.
  unfold R.v6, N.v6.
  rewrite ?node_11511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51846 (s : N.State) (i : N.Inputs) :
  R.v51846 (state s) (inputs i) = Zmod.unsigned (N.v51846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51846 s i)) at 1.
  unfold R.v51846, N.v51846.
  unfold R.v6, N.v6.
  rewrite ?node_11508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51847 (s : N.State) (i : N.Inputs) :
  R.v51847 (state s) (inputs i) = Zmod.unsigned (N.v51847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51847 s i)) at 1.
  unfold R.v51847, N.v51847.
  rewrite ?node_51845.
  rewrite ?node_51846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51848 (s : N.State) (i : N.Inputs) :
  R.v51848 (state s) (inputs i) = Zmod.unsigned (N.v51848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51848 s i)) at 1.
  unfold R.v51848, N.v51848.
  unfold R.v16484, N.v16484.
  rewrite ?node_51847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51849 (s : N.State) (i : N.Inputs) :
  R.v51849 (state s) (inputs i) = Zmod.unsigned (N.v51849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51849 s i)) at 1.
  unfold R.v51849, N.v51849.
  rewrite ?node_51844.
  rewrite ?node_51848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51850 (s : N.State) (i : N.Inputs) :
  R.v51850 (state s) (inputs i) = Zmod.unsigned (N.v51850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51850 s i)) at 1.
  unfold R.v51850, N.v51850.
  unfold R.v6, N.v6.
  rewrite ?node_51849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51851 (s : N.State) (i : N.Inputs) :
  R.v51851 (state s) (inputs i) = Zmod.unsigned (N.v51851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51851 s i)) at 1.
  unfold R.v51851, N.v51851.
  rewrite ?node_11516.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51852 (s : N.State) (i : N.Inputs) :
  R.v51852 (state s) (inputs i) = Zmod.unsigned (N.v51852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51852 s i)) at 1.
  unfold R.v51852, N.v51852.
  unfold R.v6, N.v6.
  rewrite ?node_11672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51853 (s : N.State) (i : N.Inputs) :
  R.v51853 (state s) (inputs i) = Zmod.unsigned (N.v51853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51853 s i)) at 1.
  unfold R.v51853, N.v51853.
  rewrite ?node_51851.
  rewrite ?node_51852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51854 (s : N.State) (i : N.Inputs) :
  R.v51854 (state s) (inputs i) = Zmod.unsigned (N.v51854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51854 s i)) at 1.
  unfold R.v51854, N.v51854.
  rewrite ?node_51850.
  rewrite ?node_51853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51855 (s : N.State) (i : N.Inputs) :
  R.v51855 (state s) (inputs i) = Zmod.unsigned (N.v51855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51855 s i)) at 1.
  unfold R.v51855, N.v51855.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51856 (s : N.State) (i : N.Inputs) :
  R.v51856 (state s) (inputs i) = Zmod.unsigned (N.v51856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51856 s i)) at 1.
  unfold R.v51856, N.v51856.
  rewrite ?node_11523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51857 (s : N.State) (i : N.Inputs) :
  R.v51857 (state s) (inputs i) = Zmod.unsigned (N.v51857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51857 s i)) at 1.
  unfold R.v51857, N.v51857.
  unfold R.v6, N.v6.
  rewrite ?node_11519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51858 (s : N.State) (i : N.Inputs) :
  R.v51858 (state s) (inputs i) = Zmod.unsigned (N.v51858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51858 s i)) at 1.
  unfold R.v51858, N.v51858.
  unfold R.v6, N.v6.
  rewrite ?node_11516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51859 (s : N.State) (i : N.Inputs) :
  R.v51859 (state s) (inputs i) = Zmod.unsigned (N.v51859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51859 s i)) at 1.
  unfold R.v51859, N.v51859.
  rewrite ?node_51857.
  rewrite ?node_51858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51860 (s : N.State) (i : N.Inputs) :
  R.v51860 (state s) (inputs i) = Zmod.unsigned (N.v51860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51860 s i)) at 1.
  unfold R.v51860, N.v51860.
  unfold R.v16484, N.v16484.
  rewrite ?node_51859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51861 (s : N.State) (i : N.Inputs) :
  R.v51861 (state s) (inputs i) = Zmod.unsigned (N.v51861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51861 s i)) at 1.
  unfold R.v51861, N.v51861.
  rewrite ?node_51856.
  rewrite ?node_51860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51862 (s : N.State) (i : N.Inputs) :
  R.v51862 (state s) (inputs i) = Zmod.unsigned (N.v51862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51862 s i)) at 1.
  unfold R.v51862, N.v51862.
  unfold R.v6, N.v6.
  rewrite ?node_51861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51863 (s : N.State) (i : N.Inputs) :
  R.v51863 (state s) (inputs i) = Zmod.unsigned (N.v51863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51863 s i)) at 1.
  unfold R.v51863, N.v51863.
  rewrite ?node_11524.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51864 (s : N.State) (i : N.Inputs) :
  R.v51864 (state s) (inputs i) = Zmod.unsigned (N.v51864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51864 s i)) at 1.
  unfold R.v51864, N.v51864.
  unfold R.v6, N.v6.
  rewrite ?node_11681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51865 (s : N.State) (i : N.Inputs) :
  R.v51865 (state s) (inputs i) = Zmod.unsigned (N.v51865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51865 s i)) at 1.
  unfold R.v51865, N.v51865.
  rewrite ?node_51863.
  rewrite ?node_51864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51866 (s : N.State) (i : N.Inputs) :
  R.v51866 (state s) (inputs i) = Zmod.unsigned (N.v51866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51866 s i)) at 1.
  unfold R.v51866, N.v51866.
  rewrite ?node_51862.
  rewrite ?node_51865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51867 (s : N.State) (i : N.Inputs) :
  R.v51867 (state s) (inputs i) = Zmod.unsigned (N.v51867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51867 s i)) at 1.
  unfold R.v51867, N.v51867.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51868 (s : N.State) (i : N.Inputs) :
  R.v51868 (state s) (inputs i) = Zmod.unsigned (N.v51868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51868 s i)) at 1.
  unfold R.v51868, N.v51868.
  rewrite ?node_11653.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51869 (s : N.State) (i : N.Inputs) :
  R.v51869 (state s) (inputs i) = Zmod.unsigned (N.v51869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51869 s i)) at 1.
  unfold R.v51869, N.v51869.
  rewrite ?node_11649.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51870 (s : N.State) (i : N.Inputs) :
  R.v51870 (state s) (inputs i) = Zmod.unsigned (N.v51870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51870 s i)) at 1.
  unfold R.v51870, N.v51870.
  rewrite ?node_11629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51871 (s : N.State) (i : N.Inputs) :
  R.v51871 (state s) (inputs i) = Zmod.unsigned (N.v51871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51871 s i)) at 1.
  unfold R.v51871, N.v51871.
  unfold R.v6, N.v6.
  rewrite ?node_11609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51872 (s : N.State) (i : N.Inputs) :
  R.v51872 (state s) (inputs i) = Zmod.unsigned (N.v51872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51872 s i)) at 1.
  unfold R.v51872, N.v51872.
  unfold R.v6, N.v6.
  rewrite ?node_11580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51873 (s : N.State) (i : N.Inputs) :
  R.v51873 (state s) (inputs i) = Zmod.unsigned (N.v51873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51873 s i)) at 1.
  unfold R.v51873, N.v51873.
  rewrite ?node_51871.
  rewrite ?node_51872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51874 (s : N.State) (i : N.Inputs) :
  R.v51874 (state s) (inputs i) = Zmod.unsigned (N.v51874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51874 s i)) at 1.
  unfold R.v51874, N.v51874.
  unfold R.v16484, N.v16484.
  rewrite ?node_51873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51875 (s : N.State) (i : N.Inputs) :
  R.v51875 (state s) (inputs i) = Zmod.unsigned (N.v51875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51875 s i)) at 1.
  unfold R.v51875, N.v51875.
  rewrite ?node_51868.
  rewrite ?node_51869.
  rewrite ?node_51870.
  rewrite ?node_51874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51876 (s : N.State) (i : N.Inputs) :
  R.v51876 (state s) (inputs i) = Zmod.unsigned (N.v51876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51876 s i)) at 1.
  unfold R.v51876, N.v51876.
  unfold R.v6, N.v6.
  rewrite ?node_51875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51877 (s : N.State) (i : N.Inputs) :
  R.v51877 (state s) (inputs i) = Zmod.unsigned (N.v51877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51877 s i)) at 1.
  unfold R.v51877, N.v51877.
  rewrite ?node_11654.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51878 (s : N.State) (i : N.Inputs) :
  R.v51878 (state s) (inputs i) = Zmod.unsigned (N.v51878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51878 s i)) at 1.
  unfold R.v51878, N.v51878.
  unfold R.v6, N.v6.
  rewrite ?node_11799.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51879 (s : N.State) (i : N.Inputs) :
  R.v51879 (state s) (inputs i) = Zmod.unsigned (N.v51879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51879 s i)) at 1.
  unfold R.v51879, N.v51879.
  unfold R.v6, N.v6.
  rewrite ?node_11823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51880 (s : N.State) (i : N.Inputs) :
  R.v51880 (state s) (inputs i) = Zmod.unsigned (N.v51880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51880 s i)) at 1.
  unfold R.v51880, N.v51880.
  rewrite ?node_51877.
  rewrite ?node_51878.
  rewrite ?node_51879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51881 (s : N.State) (i : N.Inputs) :
  R.v51881 (state s) (inputs i) = Zmod.unsigned (N.v51881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51881 s i)) at 1.
  unfold R.v51881, N.v51881.
  rewrite ?node_51876.
  rewrite ?node_51880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51882 (s : N.State) (i : N.Inputs) :
  R.v51882 (state s) (inputs i) = Zmod.unsigned (N.v51882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51882 s i)) at 1.
  unfold R.v51882, N.v51882.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51883 (s : N.State) (i : N.Inputs) :
  R.v51883 (state s) (inputs i) = Zmod.unsigned (N.v51883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51883 s i)) at 1.
  unfold R.v51883, N.v51883.
  rewrite ?node_11629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51884 (s : N.State) (i : N.Inputs) :
  R.v51884 (state s) (inputs i) = Zmod.unsigned (N.v51884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51884 s i)) at 1.
  unfold R.v51884, N.v51884.
  unfold R.v6, N.v6.
  rewrite ?node_11609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51885 (s : N.State) (i : N.Inputs) :
  R.v51885 (state s) (inputs i) = Zmod.unsigned (N.v51885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51885 s i)) at 1.
  unfold R.v51885, N.v51885.
  unfold R.v6, N.v6.
  rewrite ?node_11580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51886 (s : N.State) (i : N.Inputs) :
  R.v51886 (state s) (inputs i) = Zmod.unsigned (N.v51886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51886 s i)) at 1.
  unfold R.v51886, N.v51886.
  rewrite ?node_51884.
  rewrite ?node_51885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51887 (s : N.State) (i : N.Inputs) :
  R.v51887 (state s) (inputs i) = Zmod.unsigned (N.v51887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51887 s i)) at 1.
  unfold R.v51887, N.v51887.
  unfold R.v16484, N.v16484.
  rewrite ?node_51886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51888 (s : N.State) (i : N.Inputs) :
  R.v51888 (state s) (inputs i) = Zmod.unsigned (N.v51888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51888 s i)) at 1.
  unfold R.v51888, N.v51888.
  rewrite ?node_51883.
  rewrite ?node_51887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51889 (s : N.State) (i : N.Inputs) :
  R.v51889 (state s) (inputs i) = Zmod.unsigned (N.v51889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51889 s i)) at 1.
  unfold R.v51889, N.v51889.
  unfold R.v6, N.v6.
  rewrite ?node_51888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51890 (s : N.State) (i : N.Inputs) :
  R.v51890 (state s) (inputs i) = Zmod.unsigned (N.v51890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51890 s i)) at 1.
  unfold R.v51890, N.v51890.
  rewrite ?node_11630.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51891 (s : N.State) (i : N.Inputs) :
  R.v51891 (state s) (inputs i) = Zmod.unsigned (N.v51891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51891 s i)) at 1.
  unfold R.v51891, N.v51891.
  unfold R.v6, N.v6.
  rewrite ?node_11799.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51892 (s : N.State) (i : N.Inputs) :
  R.v51892 (state s) (inputs i) = Zmod.unsigned (N.v51892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51892 s i)) at 1.
  unfold R.v51892, N.v51892.
  rewrite ?node_51890.
  rewrite ?node_51891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51893 (s : N.State) (i : N.Inputs) :
  R.v51893 (state s) (inputs i) = Zmod.unsigned (N.v51893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51893 s i)) at 1.
  unfold R.v51893, N.v51893.
  rewrite ?node_51889.
  rewrite ?node_51892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51894 (s : N.State) (i : N.Inputs) :
  R.v51894 (state s) (inputs i) = Zmod.unsigned (N.v51894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51894 s i)) at 1.
  unfold R.v51894, N.v51894.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51895 (s : N.State) (i : N.Inputs) :
  R.v51895 (state s) (inputs i) = Zmod.unsigned (N.v51895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51895 s i)) at 1.
  unfold R.v51895, N.v51895.
  rewrite ?node_11653.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51896 (s : N.State) (i : N.Inputs) :
  R.v51896 (state s) (inputs i) = Zmod.unsigned (N.v51896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51896 s i)) at 1.
  unfold R.v51896, N.v51896.
  unfold R.v6, N.v6.
  rewrite ?node_11649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51897 (s : N.State) (i : N.Inputs) :
  R.v51897 (state s) (inputs i) = Zmod.unsigned (N.v51897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51897 s i)) at 1.
  unfold R.v51897, N.v51897.
  unfold R.v6, N.v6.
  rewrite ?node_11630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51898 (s : N.State) (i : N.Inputs) :
  R.v51898 (state s) (inputs i) = Zmod.unsigned (N.v51898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51898 s i)) at 1.
  unfold R.v51898, N.v51898.
  rewrite ?node_51896.
  rewrite ?node_51897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51899 (s : N.State) (i : N.Inputs) :
  R.v51899 (state s) (inputs i) = Zmod.unsigned (N.v51899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51899 s i)) at 1.
  unfold R.v51899, N.v51899.
  unfold R.v16484, N.v16484.
  rewrite ?node_51898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51900 (s : N.State) (i : N.Inputs) :
  R.v51900 (state s) (inputs i) = Zmod.unsigned (N.v51900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51900 s i)) at 1.
  unfold R.v51900, N.v51900.
  rewrite ?node_51895.
  rewrite ?node_51899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51901 (s : N.State) (i : N.Inputs) :
  R.v51901 (state s) (inputs i) = Zmod.unsigned (N.v51901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51901 s i)) at 1.
  unfold R.v51901, N.v51901.
  unfold R.v6, N.v6.
  rewrite ?node_51900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51902 (s : N.State) (i : N.Inputs) :
  R.v51902 (state s) (inputs i) = Zmod.unsigned (N.v51902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51902 s i)) at 1.
  unfold R.v51902, N.v51902.
  rewrite ?node_11654.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51903 (s : N.State) (i : N.Inputs) :
  R.v51903 (state s) (inputs i) = Zmod.unsigned (N.v51903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51903 s i)) at 1.
  unfold R.v51903, N.v51903.
  unfold R.v6, N.v6.
  rewrite ?node_11823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51904 (s : N.State) (i : N.Inputs) :
  R.v51904 (state s) (inputs i) = Zmod.unsigned (N.v51904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51904 s i)) at 1.
  unfold R.v51904, N.v51904.
  rewrite ?node_51902.
  rewrite ?node_51903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51905 (s : N.State) (i : N.Inputs) :
  R.v51905 (state s) (inputs i) = Zmod.unsigned (N.v51905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51905 s i)) at 1.
  unfold R.v51905, N.v51905.
  rewrite ?node_51901.
  rewrite ?node_51904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51906 (s : N.State) (i : N.Inputs) :
  R.v51906 (state s) (inputs i) = Zmod.unsigned (N.v51906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51906 s i)) at 1.
  unfold R.v51906, N.v51906.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51907 (s : N.State) (i : N.Inputs) :
  R.v51907 (state s) (inputs i) = Zmod.unsigned (N.v51907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51907 s i)) at 1.
  unfold R.v51907, N.v51907.
  rewrite ?node_11672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51908 (s : N.State) (i : N.Inputs) :
  R.v51908 (state s) (inputs i) = Zmod.unsigned (N.v51908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51908 s i)) at 1.
  unfold R.v51908, N.v51908.
  rewrite ?node_11668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51909 (s : N.State) (i : N.Inputs) :
  R.v51909 (state s) (inputs i) = Zmod.unsigned (N.v51909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51909 s i)) at 1.
  unfold R.v51909, N.v51909.
  rewrite ?node_11664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51910 (s : N.State) (i : N.Inputs) :
  R.v51910 (state s) (inputs i) = Zmod.unsigned (N.v51910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51910 s i)) at 1.
  unfold R.v51910, N.v51910.
  unfold R.v6, N.v6.
  rewrite ?node_11660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51911 (s : N.State) (i : N.Inputs) :
  R.v51911 (state s) (inputs i) = Zmod.unsigned (N.v51911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51911 s i)) at 1.
  unfold R.v51911, N.v51911.
  unfold R.v6, N.v6.
  rewrite ?node_11657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51912 (s : N.State) (i : N.Inputs) :
  R.v51912 (state s) (inputs i) = Zmod.unsigned (N.v51912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51912 s i)) at 1.
  unfold R.v51912, N.v51912.
  rewrite ?node_51910.
  rewrite ?node_51911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51913 (s : N.State) (i : N.Inputs) :
  R.v51913 (state s) (inputs i) = Zmod.unsigned (N.v51913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51913 s i)) at 1.
  unfold R.v51913, N.v51913.
  unfold R.v16484, N.v16484.
  rewrite ?node_51912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51914 (s : N.State) (i : N.Inputs) :
  R.v51914 (state s) (inputs i) = Zmod.unsigned (N.v51914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51914 s i)) at 1.
  unfold R.v51914, N.v51914.
  rewrite ?node_51907.
  rewrite ?node_51908.
  rewrite ?node_51909.
  rewrite ?node_51913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51915 (s : N.State) (i : N.Inputs) :
  R.v51915 (state s) (inputs i) = Zmod.unsigned (N.v51915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51915 s i)) at 1.
  unfold R.v51915, N.v51915.
  unfold R.v6, N.v6.
  rewrite ?node_51914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51916 (s : N.State) (i : N.Inputs) :
  R.v51916 (state s) (inputs i) = Zmod.unsigned (N.v51916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51916 s i)) at 1.
  unfold R.v51916, N.v51916.
  rewrite ?node_11673.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51917 (s : N.State) (i : N.Inputs) :
  R.v51917 (state s) (inputs i) = Zmod.unsigned (N.v51917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51917 s i)) at 1.
  unfold R.v51917, N.v51917.
  unfold R.v6, N.v6.
  rewrite ?node_11818.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51918 (s : N.State) (i : N.Inputs) :
  R.v51918 (state s) (inputs i) = Zmod.unsigned (N.v51918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51918 s i)) at 1.
  unfold R.v51918, N.v51918.
  unfold R.v6, N.v6.
  rewrite ?node_11827.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51919 (s : N.State) (i : N.Inputs) :
  R.v51919 (state s) (inputs i) = Zmod.unsigned (N.v51919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51919 s i)) at 1.
  unfold R.v51919, N.v51919.
  rewrite ?node_51916.
  rewrite ?node_51917.
  rewrite ?node_51918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51920 (s : N.State) (i : N.Inputs) :
  R.v51920 (state s) (inputs i) = Zmod.unsigned (N.v51920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51920 s i)) at 1.
  unfold R.v51920, N.v51920.
  rewrite ?node_51915.
  rewrite ?node_51919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51921 (s : N.State) (i : N.Inputs) :
  R.v51921 (state s) (inputs i) = Zmod.unsigned (N.v51921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51921 s i)) at 1.
  unfold R.v51921, N.v51921.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51922 (s : N.State) (i : N.Inputs) :
  R.v51922 (state s) (inputs i) = Zmod.unsigned (N.v51922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51922 s i)) at 1.
  unfold R.v51922, N.v51922.
  rewrite ?node_11664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51923 (s : N.State) (i : N.Inputs) :
  R.v51923 (state s) (inputs i) = Zmod.unsigned (N.v51923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51923 s i)) at 1.
  unfold R.v51923, N.v51923.
  unfold R.v6, N.v6.
  rewrite ?node_11660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51924 (s : N.State) (i : N.Inputs) :
  R.v51924 (state s) (inputs i) = Zmod.unsigned (N.v51924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51924 s i)) at 1.
  unfold R.v51924, N.v51924.
  unfold R.v6, N.v6.
  rewrite ?node_11657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51925 (s : N.State) (i : N.Inputs) :
  R.v51925 (state s) (inputs i) = Zmod.unsigned (N.v51925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51925 s i)) at 1.
  unfold R.v51925, N.v51925.
  rewrite ?node_51923.
  rewrite ?node_51924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51926 (s : N.State) (i : N.Inputs) :
  R.v51926 (state s) (inputs i) = Zmod.unsigned (N.v51926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51926 s i)) at 1.
  unfold R.v51926, N.v51926.
  unfold R.v16484, N.v16484.
  rewrite ?node_51925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51927 (s : N.State) (i : N.Inputs) :
  R.v51927 (state s) (inputs i) = Zmod.unsigned (N.v51927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51927 s i)) at 1.
  unfold R.v51927, N.v51927.
  rewrite ?node_51922.
  rewrite ?node_51926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51928 (s : N.State) (i : N.Inputs) :
  R.v51928 (state s) (inputs i) = Zmod.unsigned (N.v51928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51928 s i)) at 1.
  unfold R.v51928, N.v51928.
  unfold R.v6, N.v6.
  rewrite ?node_51927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51929 (s : N.State) (i : N.Inputs) :
  R.v51929 (state s) (inputs i) = Zmod.unsigned (N.v51929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51929 s i)) at 1.
  unfold R.v51929, N.v51929.
  rewrite ?node_11665.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51930 (s : N.State) (i : N.Inputs) :
  R.v51930 (state s) (inputs i) = Zmod.unsigned (N.v51930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51930 s i)) at 1.
  unfold R.v51930, N.v51930.
  unfold R.v6, N.v6.
  rewrite ?node_11818.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51931 (s : N.State) (i : N.Inputs) :
  R.v51931 (state s) (inputs i) = Zmod.unsigned (N.v51931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51931 s i)) at 1.
  unfold R.v51931, N.v51931.
  rewrite ?node_51929.
  rewrite ?node_51930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51932 (s : N.State) (i : N.Inputs) :
  R.v51932 (state s) (inputs i) = Zmod.unsigned (N.v51932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51932 s i)) at 1.
  unfold R.v51932, N.v51932.
  rewrite ?node_51928.
  rewrite ?node_51931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51933 (s : N.State) (i : N.Inputs) :
  R.v51933 (state s) (inputs i) = Zmod.unsigned (N.v51933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51933 s i)) at 1.
  unfold R.v51933, N.v51933.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51934 (s : N.State) (i : N.Inputs) :
  R.v51934 (state s) (inputs i) = Zmod.unsigned (N.v51934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51934 s i)) at 1.
  unfold R.v51934, N.v51934.
  rewrite ?node_11672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51935 (s : N.State) (i : N.Inputs) :
  R.v51935 (state s) (inputs i) = Zmod.unsigned (N.v51935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51935 s i)) at 1.
  unfold R.v51935, N.v51935.
  unfold R.v6, N.v6.
  rewrite ?node_11668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51936 (s : N.State) (i : N.Inputs) :
  R.v51936 (state s) (inputs i) = Zmod.unsigned (N.v51936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51936 s i)) at 1.
  unfold R.v51936, N.v51936.
  unfold R.v6, N.v6.
  rewrite ?node_11665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51937 (s : N.State) (i : N.Inputs) :
  R.v51937 (state s) (inputs i) = Zmod.unsigned (N.v51937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51937 s i)) at 1.
  unfold R.v51937, N.v51937.
  rewrite ?node_51935.
  rewrite ?node_51936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51938 (s : N.State) (i : N.Inputs) :
  R.v51938 (state s) (inputs i) = Zmod.unsigned (N.v51938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51938 s i)) at 1.
  unfold R.v51938, N.v51938.
  unfold R.v16484, N.v16484.
  rewrite ?node_51937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51939 (s : N.State) (i : N.Inputs) :
  R.v51939 (state s) (inputs i) = Zmod.unsigned (N.v51939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51939 s i)) at 1.
  unfold R.v51939, N.v51939.
  rewrite ?node_51934.
  rewrite ?node_51938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51940 (s : N.State) (i : N.Inputs) :
  R.v51940 (state s) (inputs i) = Zmod.unsigned (N.v51940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51940 s i)) at 1.
  unfold R.v51940, N.v51940.
  unfold R.v6, N.v6.
  rewrite ?node_51939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51941 (s : N.State) (i : N.Inputs) :
  R.v51941 (state s) (inputs i) = Zmod.unsigned (N.v51941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51941 s i)) at 1.
  unfold R.v51941, N.v51941.
  rewrite ?node_11673.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51942 (s : N.State) (i : N.Inputs) :
  R.v51942 (state s) (inputs i) = Zmod.unsigned (N.v51942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51942 s i)) at 1.
  unfold R.v51942, N.v51942.
  unfold R.v6, N.v6.
  rewrite ?node_11827.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51943 (s : N.State) (i : N.Inputs) :
  R.v51943 (state s) (inputs i) = Zmod.unsigned (N.v51943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51943 s i)) at 1.
  unfold R.v51943, N.v51943.
  rewrite ?node_51941.
  rewrite ?node_51942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51944 (s : N.State) (i : N.Inputs) :
  R.v51944 (state s) (inputs i) = Zmod.unsigned (N.v51944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51944 s i)) at 1.
  unfold R.v51944, N.v51944.
  rewrite ?node_51940.
  rewrite ?node_51943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51945 (s : N.State) (i : N.Inputs) :
  R.v51945 (state s) (inputs i) = Zmod.unsigned (N.v51945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51945 s i)) at 1.
  unfold R.v51945, N.v51945.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51946 (s : N.State) (i : N.Inputs) :
  R.v51946 (state s) (inputs i) = Zmod.unsigned (N.v51946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51946 s i)) at 1.
  unfold R.v51946, N.v51946.
  rewrite ?node_11799.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51947 (s : N.State) (i : N.Inputs) :
  R.v51947 (state s) (inputs i) = Zmod.unsigned (N.v51947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51947 s i)) at 1.
  unfold R.v51947, N.v51947.
  rewrite ?node_11795.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51948 (s : N.State) (i : N.Inputs) :
  R.v51948 (state s) (inputs i) = Zmod.unsigned (N.v51948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51948 s i)) at 1.
  unfold R.v51948, N.v51948.
  rewrite ?node_11777.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51949 (s : N.State) (i : N.Inputs) :
  R.v51949 (state s) (inputs i) = Zmod.unsigned (N.v51949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51949 s i)) at 1.
  unfold R.v51949, N.v51949.
  unfold R.v6, N.v6.
  rewrite ?node_11757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51950 (s : N.State) (i : N.Inputs) :
  R.v51950 (state s) (inputs i) = Zmod.unsigned (N.v51950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51950 s i)) at 1.
  unfold R.v51950, N.v51950.
  unfold R.v6, N.v6.
  rewrite ?node_11728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51951 (s : N.State) (i : N.Inputs) :
  R.v51951 (state s) (inputs i) = Zmod.unsigned (N.v51951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51951 s i)) at 1.
  unfold R.v51951, N.v51951.
  rewrite ?node_51949.
  rewrite ?node_51950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51952 (s : N.State) (i : N.Inputs) :
  R.v51952 (state s) (inputs i) = Zmod.unsigned (N.v51952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51952 s i)) at 1.
  unfold R.v51952, N.v51952.
  unfold R.v16484, N.v16484.
  rewrite ?node_51951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51953 (s : N.State) (i : N.Inputs) :
  R.v51953 (state s) (inputs i) = Zmod.unsigned (N.v51953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51953 s i)) at 1.
  unfold R.v51953, N.v51953.
  rewrite ?node_51946.
  rewrite ?node_51947.
  rewrite ?node_51948.
  rewrite ?node_51952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51954 (s : N.State) (i : N.Inputs) :
  R.v51954 (state s) (inputs i) = Zmod.unsigned (N.v51954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51954 s i)) at 1.
  unfold R.v51954, N.v51954.
  unfold R.v6, N.v6.
  rewrite ?node_51953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51955 (s : N.State) (i : N.Inputs) :
  R.v51955 (state s) (inputs i) = Zmod.unsigned (N.v51955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51955 s i)) at 1.
  unfold R.v51955, N.v51955.
  rewrite ?node_11800.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51956 (s : N.State) (i : N.Inputs) :
  R.v51956 (state s) (inputs i) = Zmod.unsigned (N.v51956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51956 s i)) at 1.
  unfold R.v51956, N.v51956.
  unfold R.v6, N.v6.
  rewrite ?node_11943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51957 (s : N.State) (i : N.Inputs) :
  R.v51957 (state s) (inputs i) = Zmod.unsigned (N.v51957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51957 s i)) at 1.
  unfold R.v51957, N.v51957.
  unfold R.v6, N.v6.
  rewrite ?node_11967.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51958 (s : N.State) (i : N.Inputs) :
  R.v51958 (state s) (inputs i) = Zmod.unsigned (N.v51958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51958 s i)) at 1.
  unfold R.v51958, N.v51958.
  rewrite ?node_51955.
  rewrite ?node_51956.
  rewrite ?node_51957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51959 (s : N.State) (i : N.Inputs) :
  R.v51959 (state s) (inputs i) = Zmod.unsigned (N.v51959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51959 s i)) at 1.
  unfold R.v51959, N.v51959.
  rewrite ?node_51954.
  rewrite ?node_51958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51960 (s : N.State) (i : N.Inputs) :
  R.v51960 (state s) (inputs i) = Zmod.unsigned (N.v51960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51960 s i)) at 1.
  unfold R.v51960, N.v51960.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51961 (s : N.State) (i : N.Inputs) :
  R.v51961 (state s) (inputs i) = Zmod.unsigned (N.v51961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51961 s i)) at 1.
  unfold R.v51961, N.v51961.
  rewrite ?node_11777.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51962 (s : N.State) (i : N.Inputs) :
  R.v51962 (state s) (inputs i) = Zmod.unsigned (N.v51962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51962 s i)) at 1.
  unfold R.v51962, N.v51962.
  unfold R.v6, N.v6.
  rewrite ?node_11757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51963 (s : N.State) (i : N.Inputs) :
  R.v51963 (state s) (inputs i) = Zmod.unsigned (N.v51963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51963 s i)) at 1.
  unfold R.v51963, N.v51963.
  unfold R.v6, N.v6.
  rewrite ?node_11728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51964 (s : N.State) (i : N.Inputs) :
  R.v51964 (state s) (inputs i) = Zmod.unsigned (N.v51964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51964 s i)) at 1.
  unfold R.v51964, N.v51964.
  rewrite ?node_51962.
  rewrite ?node_51963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51965 (s : N.State) (i : N.Inputs) :
  R.v51965 (state s) (inputs i) = Zmod.unsigned (N.v51965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51965 s i)) at 1.
  unfold R.v51965, N.v51965.
  unfold R.v16484, N.v16484.
  rewrite ?node_51964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51966 (s : N.State) (i : N.Inputs) :
  R.v51966 (state s) (inputs i) = Zmod.unsigned (N.v51966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51966 s i)) at 1.
  unfold R.v51966, N.v51966.
  rewrite ?node_51961.
  rewrite ?node_51965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51967 (s : N.State) (i : N.Inputs) :
  R.v51967 (state s) (inputs i) = Zmod.unsigned (N.v51967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51967 s i)) at 1.
  unfold R.v51967, N.v51967.
  unfold R.v6, N.v6.
  rewrite ?node_51966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51968 (s : N.State) (i : N.Inputs) :
  R.v51968 (state s) (inputs i) = Zmod.unsigned (N.v51968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51968 s i)) at 1.
  unfold R.v51968, N.v51968.
  rewrite ?node_11778.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51969 (s : N.State) (i : N.Inputs) :
  R.v51969 (state s) (inputs i) = Zmod.unsigned (N.v51969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51969 s i)) at 1.
  unfold R.v51969, N.v51969.
  unfold R.v6, N.v6.
  rewrite ?node_11943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51970 (s : N.State) (i : N.Inputs) :
  R.v51970 (state s) (inputs i) = Zmod.unsigned (N.v51970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51970 s i)) at 1.
  unfold R.v51970, N.v51970.
  rewrite ?node_51968.
  rewrite ?node_51969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51971 (s : N.State) (i : N.Inputs) :
  R.v51971 (state s) (inputs i) = Zmod.unsigned (N.v51971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51971 s i)) at 1.
  unfold R.v51971, N.v51971.
  rewrite ?node_51967.
  rewrite ?node_51970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51972 (s : N.State) (i : N.Inputs) :
  R.v51972 (state s) (inputs i) = Zmod.unsigned (N.v51972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51972 s i)) at 1.
  unfold R.v51972, N.v51972.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51973 (s : N.State) (i : N.Inputs) :
  R.v51973 (state s) (inputs i) = Zmod.unsigned (N.v51973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51973 s i)) at 1.
  unfold R.v51973, N.v51973.
  rewrite ?node_11799.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51974 (s : N.State) (i : N.Inputs) :
  R.v51974 (state s) (inputs i) = Zmod.unsigned (N.v51974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51974 s i)) at 1.
  unfold R.v51974, N.v51974.
  unfold R.v6, N.v6.
  rewrite ?node_11795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51975 (s : N.State) (i : N.Inputs) :
  R.v51975 (state s) (inputs i) = Zmod.unsigned (N.v51975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51975 s i)) at 1.
  unfold R.v51975, N.v51975.
  unfold R.v6, N.v6.
  rewrite ?node_11778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51976 (s : N.State) (i : N.Inputs) :
  R.v51976 (state s) (inputs i) = Zmod.unsigned (N.v51976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51976 s i)) at 1.
  unfold R.v51976, N.v51976.
  rewrite ?node_51974.
  rewrite ?node_51975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51977 (s : N.State) (i : N.Inputs) :
  R.v51977 (state s) (inputs i) = Zmod.unsigned (N.v51977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51977 s i)) at 1.
  unfold R.v51977, N.v51977.
  unfold R.v16484, N.v16484.
  rewrite ?node_51976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51978 (s : N.State) (i : N.Inputs) :
  R.v51978 (state s) (inputs i) = Zmod.unsigned (N.v51978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51978 s i)) at 1.
  unfold R.v51978, N.v51978.
  rewrite ?node_51973.
  rewrite ?node_51977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51979 (s : N.State) (i : N.Inputs) :
  R.v51979 (state s) (inputs i) = Zmod.unsigned (N.v51979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51979 s i)) at 1.
  unfold R.v51979, N.v51979.
  unfold R.v6, N.v6.
  rewrite ?node_51978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51980 (s : N.State) (i : N.Inputs) :
  R.v51980 (state s) (inputs i) = Zmod.unsigned (N.v51980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51980 s i)) at 1.
  unfold R.v51980, N.v51980.
  rewrite ?node_11800.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51981 (s : N.State) (i : N.Inputs) :
  R.v51981 (state s) (inputs i) = Zmod.unsigned (N.v51981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51981 s i)) at 1.
  unfold R.v51981, N.v51981.
  unfold R.v6, N.v6.
  rewrite ?node_11967.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51982 (s : N.State) (i : N.Inputs) :
  R.v51982 (state s) (inputs i) = Zmod.unsigned (N.v51982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51982 s i)) at 1.
  unfold R.v51982, N.v51982.
  rewrite ?node_51980.
  rewrite ?node_51981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51983 (s : N.State) (i : N.Inputs) :
  R.v51983 (state s) (inputs i) = Zmod.unsigned (N.v51983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51983 s i)) at 1.
  unfold R.v51983, N.v51983.
  rewrite ?node_51979.
  rewrite ?node_51982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51984 (s : N.State) (i : N.Inputs) :
  R.v51984 (state s) (inputs i) = Zmod.unsigned (N.v51984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51984 s i)) at 1.
  unfold R.v51984, N.v51984.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51985 (s : N.State) (i : N.Inputs) :
  R.v51985 (state s) (inputs i) = Zmod.unsigned (N.v51985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51985 s i)) at 1.
  unfold R.v51985, N.v51985.
  rewrite ?node_11818.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51986 (s : N.State) (i : N.Inputs) :
  R.v51986 (state s) (inputs i) = Zmod.unsigned (N.v51986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51986 s i)) at 1.
  unfold R.v51986, N.v51986.
  rewrite ?node_11814.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51987 (s : N.State) (i : N.Inputs) :
  R.v51987 (state s) (inputs i) = Zmod.unsigned (N.v51987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51987 s i)) at 1.
  unfold R.v51987, N.v51987.
  rewrite ?node_11810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51988 (s : N.State) (i : N.Inputs) :
  R.v51988 (state s) (inputs i) = Zmod.unsigned (N.v51988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51988 s i)) at 1.
  unfold R.v51988, N.v51988.
  unfold R.v6, N.v6.
  rewrite ?node_11806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51989 (s : N.State) (i : N.Inputs) :
  R.v51989 (state s) (inputs i) = Zmod.unsigned (N.v51989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51989 s i)) at 1.
  unfold R.v51989, N.v51989.
  unfold R.v6, N.v6.
  rewrite ?node_11803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51990 (s : N.State) (i : N.Inputs) :
  R.v51990 (state s) (inputs i) = Zmod.unsigned (N.v51990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51990 s i)) at 1.
  unfold R.v51990, N.v51990.
  rewrite ?node_51988.
  rewrite ?node_51989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51991 (s : N.State) (i : N.Inputs) :
  R.v51991 (state s) (inputs i) = Zmod.unsigned (N.v51991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51991 s i)) at 1.
  unfold R.v51991, N.v51991.
  unfold R.v16484, N.v16484.
  rewrite ?node_51990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51992 (s : N.State) (i : N.Inputs) :
  R.v51992 (state s) (inputs i) = Zmod.unsigned (N.v51992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51992 s i)) at 1.
  unfold R.v51992, N.v51992.
  rewrite ?node_51985.
  rewrite ?node_51986.
  rewrite ?node_51987.
  rewrite ?node_51991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51993 (s : N.State) (i : N.Inputs) :
  R.v51993 (state s) (inputs i) = Zmod.unsigned (N.v51993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51993 s i)) at 1.
  unfold R.v51993, N.v51993.
  unfold R.v6, N.v6.
  rewrite ?node_51992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51994 (s : N.State) (i : N.Inputs) :
  R.v51994 (state s) (inputs i) = Zmod.unsigned (N.v51994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51994 s i)) at 1.
  unfold R.v51994, N.v51994.
  rewrite ?node_11819.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51995 (s : N.State) (i : N.Inputs) :
  R.v51995 (state s) (inputs i) = Zmod.unsigned (N.v51995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51995 s i)) at 1.
  unfold R.v51995, N.v51995.
  unfold R.v6, N.v6.
  rewrite ?node_11962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51996 (s : N.State) (i : N.Inputs) :
  R.v51996 (state s) (inputs i) = Zmod.unsigned (N.v51996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51996 s i)) at 1.
  unfold R.v51996, N.v51996.
  unfold R.v6, N.v6.
  rewrite ?node_11971.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51997 (s : N.State) (i : N.Inputs) :
  R.v51997 (state s) (inputs i) = Zmod.unsigned (N.v51997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51997 s i)) at 1.
  unfold R.v51997, N.v51997.
  rewrite ?node_51994.
  rewrite ?node_51995.
  rewrite ?node_51996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51998 (s : N.State) (i : N.Inputs) :
  R.v51998 (state s) (inputs i) = Zmod.unsigned (N.v51998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51998 s i)) at 1.
  unfold R.v51998, N.v51998.
  rewrite ?node_51993.
  rewrite ?node_51997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51999 (s : N.State) (i : N.Inputs) :
  R.v51999 (state s) (inputs i) = Zmod.unsigned (N.v51999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51999 s i)) at 1.
  unfold R.v51999, N.v51999.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
