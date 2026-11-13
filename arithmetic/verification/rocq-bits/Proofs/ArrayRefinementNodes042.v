(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes041.
Lemma node_42000 (s : N.State) (i : N.Inputs) :
  R.v42000 (state s) (inputs i) = Zmod.unsigned (N.v42000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42000 s i)) at 1.
  unfold R.v42000, N.v42000.
  unfold R.v16484, N.v16484.
  rewrite ?node_41999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42001 (s : N.State) (i : N.Inputs) :
  R.v42001 (state s) (inputs i) = Zmod.unsigned (N.v42001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42001 s i)) at 1.
  unfold R.v42001, N.v42001.
  rewrite ?node_41996.
  rewrite ?node_42000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42002 (s : N.State) (i : N.Inputs) :
  R.v42002 (state s) (inputs i) = Zmod.unsigned (N.v42002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42002 s i)) at 1.
  unfold R.v42002, N.v42002.
  unfold R.v6, N.v6.
  rewrite ?node_42001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42003 (s : N.State) (i : N.Inputs) :
  R.v42003 (state s) (inputs i) = Zmod.unsigned (N.v42003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42003 s i)) at 1.
  unfold R.v42003, N.v42003.
  rewrite ?node_9469.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42004 (s : N.State) (i : N.Inputs) :
  R.v42004 (state s) (inputs i) = Zmod.unsigned (N.v42004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42004 s i)) at 1.
  unfold R.v42004, N.v42004.
  unfold R.v6, N.v6.
  rewrite ?node_9621.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42005 (s : N.State) (i : N.Inputs) :
  R.v42005 (state s) (inputs i) = Zmod.unsigned (N.v42005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42005 s i)) at 1.
  unfold R.v42005, N.v42005.
  rewrite ?node_42003.
  rewrite ?node_42004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42006 (s : N.State) (i : N.Inputs) :
  R.v42006 (state s) (inputs i) = Zmod.unsigned (N.v42006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42006 s i)) at 1.
  unfold R.v42006, N.v42006.
  rewrite ?node_42002.
  rewrite ?node_42005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42007 (s : N.State) (i : N.Inputs) :
  R.v42007 (state s) (inputs i) = Zmod.unsigned (N.v42007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42007 s i)) at 1.
  unfold R.v42007, N.v42007.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42008 (s : N.State) (i : N.Inputs) :
  R.v42008 (state s) (inputs i) = Zmod.unsigned (N.v42008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42008 s i)) at 1.
  unfold R.v42008, N.v42008.
  rewrite ?node_9474.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42009 (s : N.State) (i : N.Inputs) :
  R.v42009 (state s) (inputs i) = Zmod.unsigned (N.v42009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42009 s i)) at 1.
  unfold R.v42009, N.v42009.
  unfold R.v6, N.v6.
  rewrite ?node_9470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42010 (s : N.State) (i : N.Inputs) :
  R.v42010 (state s) (inputs i) = Zmod.unsigned (N.v42010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42010 s i)) at 1.
  unfold R.v42010, N.v42010.
  unfold R.v6, N.v6.
  rewrite ?node_9469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42011 (s : N.State) (i : N.Inputs) :
  R.v42011 (state s) (inputs i) = Zmod.unsigned (N.v42011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42011 s i)) at 1.
  unfold R.v42011, N.v42011.
  rewrite ?node_42009.
  rewrite ?node_42010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42012 (s : N.State) (i : N.Inputs) :
  R.v42012 (state s) (inputs i) = Zmod.unsigned (N.v42012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42012 s i)) at 1.
  unfold R.v42012, N.v42012.
  unfold R.v16484, N.v16484.
  rewrite ?node_42011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42013 (s : N.State) (i : N.Inputs) :
  R.v42013 (state s) (inputs i) = Zmod.unsigned (N.v42013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42013 s i)) at 1.
  unfold R.v42013, N.v42013.
  rewrite ?node_42008.
  rewrite ?node_42012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42014 (s : N.State) (i : N.Inputs) :
  R.v42014 (state s) (inputs i) = Zmod.unsigned (N.v42014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42014 s i)) at 1.
  unfold R.v42014, N.v42014.
  unfold R.v6, N.v6.
  rewrite ?node_42013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42015 (s : N.State) (i : N.Inputs) :
  R.v42015 (state s) (inputs i) = Zmod.unsigned (N.v42015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42015 s i)) at 1.
  unfold R.v42015, N.v42015.
  rewrite ?node_9475.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42016 (s : N.State) (i : N.Inputs) :
  R.v42016 (state s) (inputs i) = Zmod.unsigned (N.v42016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42016 s i)) at 1.
  unfold R.v42016, N.v42016.
  unfold R.v6, N.v6.
  rewrite ?node_9641.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42017 (s : N.State) (i : N.Inputs) :
  R.v42017 (state s) (inputs i) = Zmod.unsigned (N.v42017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42017 s i)) at 1.
  unfold R.v42017, N.v42017.
  rewrite ?node_42015.
  rewrite ?node_42016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42018 (s : N.State) (i : N.Inputs) :
  R.v42018 (state s) (inputs i) = Zmod.unsigned (N.v42018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42018 s i)) at 1.
  unfold R.v42018, N.v42018.
  rewrite ?node_42014.
  rewrite ?node_42017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42019 (s : N.State) (i : N.Inputs) :
  R.v42019 (state s) (inputs i) = Zmod.unsigned (N.v42019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42019 s i)) at 1.
  unfold R.v42019, N.v42019.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42020 (s : N.State) (i : N.Inputs) :
  R.v42020 (state s) (inputs i) = Zmod.unsigned (N.v42020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42020 s i)) at 1.
  unfold R.v42020, N.v42020.
  rewrite ?node_9551.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42021 (s : N.State) (i : N.Inputs) :
  R.v42021 (state s) (inputs i) = Zmod.unsigned (N.v42021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42021 s i)) at 1.
  unfold R.v42021, N.v42021.
  rewrite ?node_9547.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42022 (s : N.State) (i : N.Inputs) :
  R.v42022 (state s) (inputs i) = Zmod.unsigned (N.v42022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42022 s i)) at 1.
  unfold R.v42022, N.v42022.
  rewrite ?node_9539.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42023 (s : N.State) (i : N.Inputs) :
  R.v42023 (state s) (inputs i) = Zmod.unsigned (N.v42023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42023 s i)) at 1.
  unfold R.v42023, N.v42023.
  unfold R.v6, N.v6.
  rewrite ?node_9531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42024 (s : N.State) (i : N.Inputs) :
  R.v42024 (state s) (inputs i) = Zmod.unsigned (N.v42024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42024 s i)) at 1.
  unfold R.v42024, N.v42024.
  unfold R.v6, N.v6.
  rewrite ?node_9524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42025 (s : N.State) (i : N.Inputs) :
  R.v42025 (state s) (inputs i) = Zmod.unsigned (N.v42025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42025 s i)) at 1.
  unfold R.v42025, N.v42025.
  rewrite ?node_42023.
  rewrite ?node_42024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42026 (s : N.State) (i : N.Inputs) :
  R.v42026 (state s) (inputs i) = Zmod.unsigned (N.v42026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42026 s i)) at 1.
  unfold R.v42026, N.v42026.
  unfold R.v16484, N.v16484.
  rewrite ?node_42025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42027 (s : N.State) (i : N.Inputs) :
  R.v42027 (state s) (inputs i) = Zmod.unsigned (N.v42027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42027 s i)) at 1.
  unfold R.v42027, N.v42027.
  rewrite ?node_42020.
  rewrite ?node_42021.
  rewrite ?node_42022.
  rewrite ?node_42026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42028 (s : N.State) (i : N.Inputs) :
  R.v42028 (state s) (inputs i) = Zmod.unsigned (N.v42028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42028 s i)) at 1.
  unfold R.v42028, N.v42028.
  unfold R.v6, N.v6.
  rewrite ?node_42027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42029 (s : N.State) (i : N.Inputs) :
  R.v42029 (state s) (inputs i) = Zmod.unsigned (N.v42029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42029 s i)) at 1.
  unfold R.v42029, N.v42029.
  rewrite ?node_9552.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42030 (s : N.State) (i : N.Inputs) :
  R.v42030 (state s) (inputs i) = Zmod.unsigned (N.v42030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42030 s i)) at 1.
  unfold R.v42030, N.v42030.
  unfold R.v6, N.v6.
  rewrite ?node_9700.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42031 (s : N.State) (i : N.Inputs) :
  R.v42031 (state s) (inputs i) = Zmod.unsigned (N.v42031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42031 s i)) at 1.
  unfold R.v42031, N.v42031.
  unfold R.v6, N.v6.
  rewrite ?node_9780.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42032 (s : N.State) (i : N.Inputs) :
  R.v42032 (state s) (inputs i) = Zmod.unsigned (N.v42032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42032 s i)) at 1.
  unfold R.v42032, N.v42032.
  rewrite ?node_42029.
  rewrite ?node_42030.
  rewrite ?node_42031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42033 (s : N.State) (i : N.Inputs) :
  R.v42033 (state s) (inputs i) = Zmod.unsigned (N.v42033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42033 s i)) at 1.
  unfold R.v42033, N.v42033.
  rewrite ?node_42028.
  rewrite ?node_42032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42034 (s : N.State) (i : N.Inputs) :
  R.v42034 (state s) (inputs i) = Zmod.unsigned (N.v42034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42034 s i)) at 1.
  unfold R.v42034, N.v42034.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42035 (s : N.State) (i : N.Inputs) :
  R.v42035 (state s) (inputs i) = Zmod.unsigned (N.v42035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42035 s i)) at 1.
  unfold R.v42035, N.v42035.
  rewrite ?node_9539.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42036 (s : N.State) (i : N.Inputs) :
  R.v42036 (state s) (inputs i) = Zmod.unsigned (N.v42036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42036 s i)) at 1.
  unfold R.v42036, N.v42036.
  unfold R.v6, N.v6.
  rewrite ?node_9531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42037 (s : N.State) (i : N.Inputs) :
  R.v42037 (state s) (inputs i) = Zmod.unsigned (N.v42037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42037 s i)) at 1.
  unfold R.v42037, N.v42037.
  unfold R.v6, N.v6.
  rewrite ?node_9524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42038 (s : N.State) (i : N.Inputs) :
  R.v42038 (state s) (inputs i) = Zmod.unsigned (N.v42038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42038 s i)) at 1.
  unfold R.v42038, N.v42038.
  rewrite ?node_42036.
  rewrite ?node_42037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42039 (s : N.State) (i : N.Inputs) :
  R.v42039 (state s) (inputs i) = Zmod.unsigned (N.v42039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42039 s i)) at 1.
  unfold R.v42039, N.v42039.
  unfold R.v16484, N.v16484.
  rewrite ?node_42038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42040 (s : N.State) (i : N.Inputs) :
  R.v42040 (state s) (inputs i) = Zmod.unsigned (N.v42040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42040 s i)) at 1.
  unfold R.v42040, N.v42040.
  rewrite ?node_42035.
  rewrite ?node_42039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42041 (s : N.State) (i : N.Inputs) :
  R.v42041 (state s) (inputs i) = Zmod.unsigned (N.v42041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42041 s i)) at 1.
  unfold R.v42041, N.v42041.
  unfold R.v6, N.v6.
  rewrite ?node_42040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42042 (s : N.State) (i : N.Inputs) :
  R.v42042 (state s) (inputs i) = Zmod.unsigned (N.v42042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42042 s i)) at 1.
  unfold R.v42042, N.v42042.
  rewrite ?node_9540.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42043 (s : N.State) (i : N.Inputs) :
  R.v42043 (state s) (inputs i) = Zmod.unsigned (N.v42043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42043 s i)) at 1.
  unfold R.v42043, N.v42043.
  unfold R.v6, N.v6.
  rewrite ?node_9700.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42044 (s : N.State) (i : N.Inputs) :
  R.v42044 (state s) (inputs i) = Zmod.unsigned (N.v42044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42044 s i)) at 1.
  unfold R.v42044, N.v42044.
  rewrite ?node_42042.
  rewrite ?node_42043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42045 (s : N.State) (i : N.Inputs) :
  R.v42045 (state s) (inputs i) = Zmod.unsigned (N.v42045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42045 s i)) at 1.
  unfold R.v42045, N.v42045.
  rewrite ?node_42041.
  rewrite ?node_42044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42046 (s : N.State) (i : N.Inputs) :
  R.v42046 (state s) (inputs i) = Zmod.unsigned (N.v42046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42046 s i)) at 1.
  unfold R.v42046, N.v42046.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42047 (s : N.State) (i : N.Inputs) :
  R.v42047 (state s) (inputs i) = Zmod.unsigned (N.v42047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42047 s i)) at 1.
  unfold R.v42047, N.v42047.
  rewrite ?node_9551.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42048 (s : N.State) (i : N.Inputs) :
  R.v42048 (state s) (inputs i) = Zmod.unsigned (N.v42048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42048 s i)) at 1.
  unfold R.v42048, N.v42048.
  unfold R.v6, N.v6.
  rewrite ?node_9547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42049 (s : N.State) (i : N.Inputs) :
  R.v42049 (state s) (inputs i) = Zmod.unsigned (N.v42049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42049 s i)) at 1.
  unfold R.v42049, N.v42049.
  unfold R.v6, N.v6.
  rewrite ?node_9540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42050 (s : N.State) (i : N.Inputs) :
  R.v42050 (state s) (inputs i) = Zmod.unsigned (N.v42050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42050 s i)) at 1.
  unfold R.v42050, N.v42050.
  rewrite ?node_42048.
  rewrite ?node_42049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42051 (s : N.State) (i : N.Inputs) :
  R.v42051 (state s) (inputs i) = Zmod.unsigned (N.v42051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42051 s i)) at 1.
  unfold R.v42051, N.v42051.
  unfold R.v16484, N.v16484.
  rewrite ?node_42050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42052 (s : N.State) (i : N.Inputs) :
  R.v42052 (state s) (inputs i) = Zmod.unsigned (N.v42052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42052 s i)) at 1.
  unfold R.v42052, N.v42052.
  rewrite ?node_42047.
  rewrite ?node_42051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42053 (s : N.State) (i : N.Inputs) :
  R.v42053 (state s) (inputs i) = Zmod.unsigned (N.v42053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42053 s i)) at 1.
  unfold R.v42053, N.v42053.
  unfold R.v6, N.v6.
  rewrite ?node_42052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42054 (s : N.State) (i : N.Inputs) :
  R.v42054 (state s) (inputs i) = Zmod.unsigned (N.v42054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42054 s i)) at 1.
  unfold R.v42054, N.v42054.
  rewrite ?node_9552.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42055 (s : N.State) (i : N.Inputs) :
  R.v42055 (state s) (inputs i) = Zmod.unsigned (N.v42055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42055 s i)) at 1.
  unfold R.v42055, N.v42055.
  unfold R.v6, N.v6.
  rewrite ?node_9780.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42056 (s : N.State) (i : N.Inputs) :
  R.v42056 (state s) (inputs i) = Zmod.unsigned (N.v42056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42056 s i)) at 1.
  unfold R.v42056, N.v42056.
  rewrite ?node_42054.
  rewrite ?node_42055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42057 (s : N.State) (i : N.Inputs) :
  R.v42057 (state s) (inputs i) = Zmod.unsigned (N.v42057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42057 s i)) at 1.
  unfold R.v42057, N.v42057.
  rewrite ?node_42053.
  rewrite ?node_42056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42058 (s : N.State) (i : N.Inputs) :
  R.v42058 (state s) (inputs i) = Zmod.unsigned (N.v42058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42058 s i)) at 1.
  unfold R.v42058, N.v42058.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42059 (s : N.State) (i : N.Inputs) :
  R.v42059 (state s) (inputs i) = Zmod.unsigned (N.v42059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42059 s i)) at 1.
  unfold R.v42059, N.v42059.
  rewrite ?node_9581.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42060 (s : N.State) (i : N.Inputs) :
  R.v42060 (state s) (inputs i) = Zmod.unsigned (N.v42060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42060 s i)) at 1.
  unfold R.v42060, N.v42060.
  rewrite ?node_9577.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42061 (s : N.State) (i : N.Inputs) :
  R.v42061 (state s) (inputs i) = Zmod.unsigned (N.v42061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42061 s i)) at 1.
  unfold R.v42061, N.v42061.
  rewrite ?node_9574.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42062 (s : N.State) (i : N.Inputs) :
  R.v42062 (state s) (inputs i) = Zmod.unsigned (N.v42062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42062 s i)) at 1.
  unfold R.v42062, N.v42062.
  unfold R.v6, N.v6.
  rewrite ?node_9566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42063 (s : N.State) (i : N.Inputs) :
  R.v42063 (state s) (inputs i) = Zmod.unsigned (N.v42063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42063 s i)) at 1.
  unfold R.v42063, N.v42063.
  unfold R.v6, N.v6.
  rewrite ?node_9559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42064 (s : N.State) (i : N.Inputs) :
  R.v42064 (state s) (inputs i) = Zmod.unsigned (N.v42064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42064 s i)) at 1.
  unfold R.v42064, N.v42064.
  rewrite ?node_42062.
  rewrite ?node_42063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42065 (s : N.State) (i : N.Inputs) :
  R.v42065 (state s) (inputs i) = Zmod.unsigned (N.v42065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42065 s i)) at 1.
  unfold R.v42065, N.v42065.
  unfold R.v16484, N.v16484.
  rewrite ?node_42064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42066 (s : N.State) (i : N.Inputs) :
  R.v42066 (state s) (inputs i) = Zmod.unsigned (N.v42066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42066 s i)) at 1.
  unfold R.v42066, N.v42066.
  rewrite ?node_42059.
  rewrite ?node_42060.
  rewrite ?node_42061.
  rewrite ?node_42065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42067 (s : N.State) (i : N.Inputs) :
  R.v42067 (state s) (inputs i) = Zmod.unsigned (N.v42067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42067 s i)) at 1.
  unfold R.v42067, N.v42067.
  unfold R.v6, N.v6.
  rewrite ?node_42066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42068 (s : N.State) (i : N.Inputs) :
  R.v42068 (state s) (inputs i) = Zmod.unsigned (N.v42068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42068 s i)) at 1.
  unfold R.v42068, N.v42068.
  rewrite ?node_9582.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42069 (s : N.State) (i : N.Inputs) :
  R.v42069 (state s) (inputs i) = Zmod.unsigned (N.v42069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42069 s i)) at 1.
  unfold R.v42069, N.v42069.
  unfold R.v6, N.v6.
  rewrite ?node_9731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42070 (s : N.State) (i : N.Inputs) :
  R.v42070 (state s) (inputs i) = Zmod.unsigned (N.v42070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42070 s i)) at 1.
  unfold R.v42070, N.v42070.
  unfold R.v6, N.v6.
  rewrite ?node_9783.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42071 (s : N.State) (i : N.Inputs) :
  R.v42071 (state s) (inputs i) = Zmod.unsigned (N.v42071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42071 s i)) at 1.
  unfold R.v42071, N.v42071.
  rewrite ?node_42068.
  rewrite ?node_42069.
  rewrite ?node_42070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42072 (s : N.State) (i : N.Inputs) :
  R.v42072 (state s) (inputs i) = Zmod.unsigned (N.v42072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42072 s i)) at 1.
  unfold R.v42072, N.v42072.
  rewrite ?node_42067.
  rewrite ?node_42071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42073 (s : N.State) (i : N.Inputs) :
  R.v42073 (state s) (inputs i) = Zmod.unsigned (N.v42073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42073 s i)) at 1.
  unfold R.v42073, N.v42073.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42074 (s : N.State) (i : N.Inputs) :
  R.v42074 (state s) (inputs i) = Zmod.unsigned (N.v42074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42074 s i)) at 1.
  unfold R.v42074, N.v42074.
  rewrite ?node_9574.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42075 (s : N.State) (i : N.Inputs) :
  R.v42075 (state s) (inputs i) = Zmod.unsigned (N.v42075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42075 s i)) at 1.
  unfold R.v42075, N.v42075.
  unfold R.v6, N.v6.
  rewrite ?node_9566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42076 (s : N.State) (i : N.Inputs) :
  R.v42076 (state s) (inputs i) = Zmod.unsigned (N.v42076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42076 s i)) at 1.
  unfold R.v42076, N.v42076.
  unfold R.v6, N.v6.
  rewrite ?node_9559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42077 (s : N.State) (i : N.Inputs) :
  R.v42077 (state s) (inputs i) = Zmod.unsigned (N.v42077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42077 s i)) at 1.
  unfold R.v42077, N.v42077.
  rewrite ?node_42075.
  rewrite ?node_42076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42078 (s : N.State) (i : N.Inputs) :
  R.v42078 (state s) (inputs i) = Zmod.unsigned (N.v42078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42078 s i)) at 1.
  unfold R.v42078, N.v42078.
  unfold R.v16484, N.v16484.
  rewrite ?node_42077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42079 (s : N.State) (i : N.Inputs) :
  R.v42079 (state s) (inputs i) = Zmod.unsigned (N.v42079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42079 s i)) at 1.
  unfold R.v42079, N.v42079.
  rewrite ?node_42074.
  rewrite ?node_42078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42080 (s : N.State) (i : N.Inputs) :
  R.v42080 (state s) (inputs i) = Zmod.unsigned (N.v42080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42080 s i)) at 1.
  unfold R.v42080, N.v42080.
  unfold R.v6, N.v6.
  rewrite ?node_42079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42081 (s : N.State) (i : N.Inputs) :
  R.v42081 (state s) (inputs i) = Zmod.unsigned (N.v42081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42081 s i)) at 1.
  unfold R.v42081, N.v42081.
  rewrite ?node_9575.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42082 (s : N.State) (i : N.Inputs) :
  R.v42082 (state s) (inputs i) = Zmod.unsigned (N.v42082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42082 s i)) at 1.
  unfold R.v42082, N.v42082.
  unfold R.v6, N.v6.
  rewrite ?node_9731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42083 (s : N.State) (i : N.Inputs) :
  R.v42083 (state s) (inputs i) = Zmod.unsigned (N.v42083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42083 s i)) at 1.
  unfold R.v42083, N.v42083.
  rewrite ?node_42081.
  rewrite ?node_42082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42084 (s : N.State) (i : N.Inputs) :
  R.v42084 (state s) (inputs i) = Zmod.unsigned (N.v42084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42084 s i)) at 1.
  unfold R.v42084, N.v42084.
  rewrite ?node_42080.
  rewrite ?node_42083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42085 (s : N.State) (i : N.Inputs) :
  R.v42085 (state s) (inputs i) = Zmod.unsigned (N.v42085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42085 s i)) at 1.
  unfold R.v42085, N.v42085.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42086 (s : N.State) (i : N.Inputs) :
  R.v42086 (state s) (inputs i) = Zmod.unsigned (N.v42086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42086 s i)) at 1.
  unfold R.v42086, N.v42086.
  rewrite ?node_9581.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42087 (s : N.State) (i : N.Inputs) :
  R.v42087 (state s) (inputs i) = Zmod.unsigned (N.v42087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42087 s i)) at 1.
  unfold R.v42087, N.v42087.
  unfold R.v6, N.v6.
  rewrite ?node_9577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42088 (s : N.State) (i : N.Inputs) :
  R.v42088 (state s) (inputs i) = Zmod.unsigned (N.v42088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42088 s i)) at 1.
  unfold R.v42088, N.v42088.
  unfold R.v6, N.v6.
  rewrite ?node_9575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42089 (s : N.State) (i : N.Inputs) :
  R.v42089 (state s) (inputs i) = Zmod.unsigned (N.v42089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42089 s i)) at 1.
  unfold R.v42089, N.v42089.
  rewrite ?node_42087.
  rewrite ?node_42088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42090 (s : N.State) (i : N.Inputs) :
  R.v42090 (state s) (inputs i) = Zmod.unsigned (N.v42090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42090 s i)) at 1.
  unfold R.v42090, N.v42090.
  unfold R.v16484, N.v16484.
  rewrite ?node_42089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42091 (s : N.State) (i : N.Inputs) :
  R.v42091 (state s) (inputs i) = Zmod.unsigned (N.v42091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42091 s i)) at 1.
  unfold R.v42091, N.v42091.
  rewrite ?node_42086.
  rewrite ?node_42090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42092 (s : N.State) (i : N.Inputs) :
  R.v42092 (state s) (inputs i) = Zmod.unsigned (N.v42092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42092 s i)) at 1.
  unfold R.v42092, N.v42092.
  unfold R.v6, N.v6.
  rewrite ?node_42091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42093 (s : N.State) (i : N.Inputs) :
  R.v42093 (state s) (inputs i) = Zmod.unsigned (N.v42093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42093 s i)) at 1.
  unfold R.v42093, N.v42093.
  rewrite ?node_9582.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42094 (s : N.State) (i : N.Inputs) :
  R.v42094 (state s) (inputs i) = Zmod.unsigned (N.v42094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42094 s i)) at 1.
  unfold R.v42094, N.v42094.
  unfold R.v6, N.v6.
  rewrite ?node_9783.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42095 (s : N.State) (i : N.Inputs) :
  R.v42095 (state s) (inputs i) = Zmod.unsigned (N.v42095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42095 s i)) at 1.
  unfold R.v42095, N.v42095.
  rewrite ?node_42093.
  rewrite ?node_42094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42096 (s : N.State) (i : N.Inputs) :
  R.v42096 (state s) (inputs i) = Zmod.unsigned (N.v42096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42096 s i)) at 1.
  unfold R.v42096, N.v42096.
  rewrite ?node_42092.
  rewrite ?node_42095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42097 (s : N.State) (i : N.Inputs) :
  R.v42097 (state s) (inputs i) = Zmod.unsigned (N.v42097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42097 s i)) at 1.
  unfold R.v42097, N.v42097.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42098 (s : N.State) (i : N.Inputs) :
  R.v42098 (state s) (inputs i) = Zmod.unsigned (N.v42098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42098 s i)) at 1.
  unfold R.v42098, N.v42098.
  rewrite ?node_9601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42099 (s : N.State) (i : N.Inputs) :
  R.v42099 (state s) (inputs i) = Zmod.unsigned (N.v42099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42099 s i)) at 1.
  unfold R.v42099, N.v42099.
  rewrite ?node_9597.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42100 (s : N.State) (i : N.Inputs) :
  R.v42100 (state s) (inputs i) = Zmod.unsigned (N.v42100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42100 s i)) at 1.
  unfold R.v42100, N.v42100.
  rewrite ?node_9593.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42101 (s : N.State) (i : N.Inputs) :
  R.v42101 (state s) (inputs i) = Zmod.unsigned (N.v42101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42101 s i)) at 1.
  unfold R.v42101, N.v42101.
  unfold R.v6, N.v6.
  rewrite ?node_9589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42102 (s : N.State) (i : N.Inputs) :
  R.v42102 (state s) (inputs i) = Zmod.unsigned (N.v42102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42102 s i)) at 1.
  unfold R.v42102, N.v42102.
  unfold R.v6, N.v6.
  rewrite ?node_9586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42103 (s : N.State) (i : N.Inputs) :
  R.v42103 (state s) (inputs i) = Zmod.unsigned (N.v42103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42103 s i)) at 1.
  unfold R.v42103, N.v42103.
  rewrite ?node_42101.
  rewrite ?node_42102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42104 (s : N.State) (i : N.Inputs) :
  R.v42104 (state s) (inputs i) = Zmod.unsigned (N.v42104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42104 s i)) at 1.
  unfold R.v42104, N.v42104.
  unfold R.v16484, N.v16484.
  rewrite ?node_42103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42105 (s : N.State) (i : N.Inputs) :
  R.v42105 (state s) (inputs i) = Zmod.unsigned (N.v42105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42105 s i)) at 1.
  unfold R.v42105, N.v42105.
  rewrite ?node_42098.
  rewrite ?node_42099.
  rewrite ?node_42100.
  rewrite ?node_42104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42106 (s : N.State) (i : N.Inputs) :
  R.v42106 (state s) (inputs i) = Zmod.unsigned (N.v42106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42106 s i)) at 1.
  unfold R.v42106, N.v42106.
  unfold R.v6, N.v6.
  rewrite ?node_42105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42107 (s : N.State) (i : N.Inputs) :
  R.v42107 (state s) (inputs i) = Zmod.unsigned (N.v42107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42107 s i)) at 1.
  unfold R.v42107, N.v42107.
  rewrite ?node_9602.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42108 (s : N.State) (i : N.Inputs) :
  R.v42108 (state s) (inputs i) = Zmod.unsigned (N.v42108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42108 s i)) at 1.
  unfold R.v42108, N.v42108.
  unfold R.v6, N.v6.
  rewrite ?node_9751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42109 (s : N.State) (i : N.Inputs) :
  R.v42109 (state s) (inputs i) = Zmod.unsigned (N.v42109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42109 s i)) at 1.
  unfold R.v42109, N.v42109.
  unfold R.v6, N.v6.
  rewrite ?node_9787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42110 (s : N.State) (i : N.Inputs) :
  R.v42110 (state s) (inputs i) = Zmod.unsigned (N.v42110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42110 s i)) at 1.
  unfold R.v42110, N.v42110.
  rewrite ?node_42107.
  rewrite ?node_42108.
  rewrite ?node_42109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42111 (s : N.State) (i : N.Inputs) :
  R.v42111 (state s) (inputs i) = Zmod.unsigned (N.v42111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42111 s i)) at 1.
  unfold R.v42111, N.v42111.
  rewrite ?node_42106.
  rewrite ?node_42110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42112 (s : N.State) (i : N.Inputs) :
  R.v42112 (state s) (inputs i) = Zmod.unsigned (N.v42112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42112 s i)) at 1.
  unfold R.v42112, N.v42112.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42113 (s : N.State) (i : N.Inputs) :
  R.v42113 (state s) (inputs i) = Zmod.unsigned (N.v42113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42113 s i)) at 1.
  unfold R.v42113, N.v42113.
  rewrite ?node_9593.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42114 (s : N.State) (i : N.Inputs) :
  R.v42114 (state s) (inputs i) = Zmod.unsigned (N.v42114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42114 s i)) at 1.
  unfold R.v42114, N.v42114.
  unfold R.v6, N.v6.
  rewrite ?node_9589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42115 (s : N.State) (i : N.Inputs) :
  R.v42115 (state s) (inputs i) = Zmod.unsigned (N.v42115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42115 s i)) at 1.
  unfold R.v42115, N.v42115.
  unfold R.v6, N.v6.
  rewrite ?node_9586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42116 (s : N.State) (i : N.Inputs) :
  R.v42116 (state s) (inputs i) = Zmod.unsigned (N.v42116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42116 s i)) at 1.
  unfold R.v42116, N.v42116.
  rewrite ?node_42114.
  rewrite ?node_42115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42117 (s : N.State) (i : N.Inputs) :
  R.v42117 (state s) (inputs i) = Zmod.unsigned (N.v42117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42117 s i)) at 1.
  unfold R.v42117, N.v42117.
  unfold R.v16484, N.v16484.
  rewrite ?node_42116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42118 (s : N.State) (i : N.Inputs) :
  R.v42118 (state s) (inputs i) = Zmod.unsigned (N.v42118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42118 s i)) at 1.
  unfold R.v42118, N.v42118.
  rewrite ?node_42113.
  rewrite ?node_42117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42119 (s : N.State) (i : N.Inputs) :
  R.v42119 (state s) (inputs i) = Zmod.unsigned (N.v42119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42119 s i)) at 1.
  unfold R.v42119, N.v42119.
  unfold R.v6, N.v6.
  rewrite ?node_42118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42120 (s : N.State) (i : N.Inputs) :
  R.v42120 (state s) (inputs i) = Zmod.unsigned (N.v42120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42120 s i)) at 1.
  unfold R.v42120, N.v42120.
  rewrite ?node_9594.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42121 (s : N.State) (i : N.Inputs) :
  R.v42121 (state s) (inputs i) = Zmod.unsigned (N.v42121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42121 s i)) at 1.
  unfold R.v42121, N.v42121.
  unfold R.v6, N.v6.
  rewrite ?node_9751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42122 (s : N.State) (i : N.Inputs) :
  R.v42122 (state s) (inputs i) = Zmod.unsigned (N.v42122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42122 s i)) at 1.
  unfold R.v42122, N.v42122.
  rewrite ?node_42120.
  rewrite ?node_42121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42123 (s : N.State) (i : N.Inputs) :
  R.v42123 (state s) (inputs i) = Zmod.unsigned (N.v42123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42123 s i)) at 1.
  unfold R.v42123, N.v42123.
  rewrite ?node_42119.
  rewrite ?node_42122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42124 (s : N.State) (i : N.Inputs) :
  R.v42124 (state s) (inputs i) = Zmod.unsigned (N.v42124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42124 s i)) at 1.
  unfold R.v42124, N.v42124.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42125 (s : N.State) (i : N.Inputs) :
  R.v42125 (state s) (inputs i) = Zmod.unsigned (N.v42125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42125 s i)) at 1.
  unfold R.v42125, N.v42125.
  rewrite ?node_9601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42126 (s : N.State) (i : N.Inputs) :
  R.v42126 (state s) (inputs i) = Zmod.unsigned (N.v42126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42126 s i)) at 1.
  unfold R.v42126, N.v42126.
  unfold R.v6, N.v6.
  rewrite ?node_9597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42127 (s : N.State) (i : N.Inputs) :
  R.v42127 (state s) (inputs i) = Zmod.unsigned (N.v42127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42127 s i)) at 1.
  unfold R.v42127, N.v42127.
  unfold R.v6, N.v6.
  rewrite ?node_9594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42128 (s : N.State) (i : N.Inputs) :
  R.v42128 (state s) (inputs i) = Zmod.unsigned (N.v42128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42128 s i)) at 1.
  unfold R.v42128, N.v42128.
  rewrite ?node_42126.
  rewrite ?node_42127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42129 (s : N.State) (i : N.Inputs) :
  R.v42129 (state s) (inputs i) = Zmod.unsigned (N.v42129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42129 s i)) at 1.
  unfold R.v42129, N.v42129.
  unfold R.v16484, N.v16484.
  rewrite ?node_42128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42130 (s : N.State) (i : N.Inputs) :
  R.v42130 (state s) (inputs i) = Zmod.unsigned (N.v42130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42130 s i)) at 1.
  unfold R.v42130, N.v42130.
  rewrite ?node_42125.
  rewrite ?node_42129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42131 (s : N.State) (i : N.Inputs) :
  R.v42131 (state s) (inputs i) = Zmod.unsigned (N.v42131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42131 s i)) at 1.
  unfold R.v42131, N.v42131.
  unfold R.v6, N.v6.
  rewrite ?node_42130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42132 (s : N.State) (i : N.Inputs) :
  R.v42132 (state s) (inputs i) = Zmod.unsigned (N.v42132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42132 s i)) at 1.
  unfold R.v42132, N.v42132.
  rewrite ?node_9602.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42133 (s : N.State) (i : N.Inputs) :
  R.v42133 (state s) (inputs i) = Zmod.unsigned (N.v42133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42133 s i)) at 1.
  unfold R.v42133, N.v42133.
  unfold R.v6, N.v6.
  rewrite ?node_9787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42134 (s : N.State) (i : N.Inputs) :
  R.v42134 (state s) (inputs i) = Zmod.unsigned (N.v42134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42134 s i)) at 1.
  unfold R.v42134, N.v42134.
  rewrite ?node_42132.
  rewrite ?node_42133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42135 (s : N.State) (i : N.Inputs) :
  R.v42135 (state s) (inputs i) = Zmod.unsigned (N.v42135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42135 s i)) at 1.
  unfold R.v42135, N.v42135.
  rewrite ?node_42131.
  rewrite ?node_42134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42136 (s : N.State) (i : N.Inputs) :
  R.v42136 (state s) (inputs i) = Zmod.unsigned (N.v42136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42136 s i)) at 1.
  unfold R.v42136, N.v42136.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42137 (s : N.State) (i : N.Inputs) :
  R.v42137 (state s) (inputs i) = Zmod.unsigned (N.v42137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42137 s i)) at 1.
  unfold R.v42137, N.v42137.
  rewrite ?node_9621.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42138 (s : N.State) (i : N.Inputs) :
  R.v42138 (state s) (inputs i) = Zmod.unsigned (N.v42138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42138 s i)) at 1.
  unfold R.v42138, N.v42138.
  rewrite ?node_9617.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42139 (s : N.State) (i : N.Inputs) :
  R.v42139 (state s) (inputs i) = Zmod.unsigned (N.v42139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42139 s i)) at 1.
  unfold R.v42139, N.v42139.
  rewrite ?node_9613.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42140 (s : N.State) (i : N.Inputs) :
  R.v42140 (state s) (inputs i) = Zmod.unsigned (N.v42140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42140 s i)) at 1.
  unfold R.v42140, N.v42140.
  unfold R.v6, N.v6.
  rewrite ?node_9609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42141 (s : N.State) (i : N.Inputs) :
  R.v42141 (state s) (inputs i) = Zmod.unsigned (N.v42141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42141 s i)) at 1.
  unfold R.v42141, N.v42141.
  unfold R.v6, N.v6.
  rewrite ?node_9606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42142 (s : N.State) (i : N.Inputs) :
  R.v42142 (state s) (inputs i) = Zmod.unsigned (N.v42142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42142 s i)) at 1.
  unfold R.v42142, N.v42142.
  rewrite ?node_42140.
  rewrite ?node_42141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42143 (s : N.State) (i : N.Inputs) :
  R.v42143 (state s) (inputs i) = Zmod.unsigned (N.v42143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42143 s i)) at 1.
  unfold R.v42143, N.v42143.
  unfold R.v16484, N.v16484.
  rewrite ?node_42142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42144 (s : N.State) (i : N.Inputs) :
  R.v42144 (state s) (inputs i) = Zmod.unsigned (N.v42144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42144 s i)) at 1.
  unfold R.v42144, N.v42144.
  rewrite ?node_42137.
  rewrite ?node_42138.
  rewrite ?node_42139.
  rewrite ?node_42143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42145 (s : N.State) (i : N.Inputs) :
  R.v42145 (state s) (inputs i) = Zmod.unsigned (N.v42145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42145 s i)) at 1.
  unfold R.v42145, N.v42145.
  unfold R.v6, N.v6.
  rewrite ?node_42144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42146 (s : N.State) (i : N.Inputs) :
  R.v42146 (state s) (inputs i) = Zmod.unsigned (N.v42146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42146 s i)) at 1.
  unfold R.v42146, N.v42146.
  rewrite ?node_9622.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42147 (s : N.State) (i : N.Inputs) :
  R.v42147 (state s) (inputs i) = Zmod.unsigned (N.v42147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42147 s i)) at 1.
  unfold R.v42147, N.v42147.
  unfold R.v6, N.v6.
  rewrite ?node_9771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42148 (s : N.State) (i : N.Inputs) :
  R.v42148 (state s) (inputs i) = Zmod.unsigned (N.v42148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42148 s i)) at 1.
  unfold R.v42148, N.v42148.
  unfold R.v6, N.v6.
  rewrite ?node_9791.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42149 (s : N.State) (i : N.Inputs) :
  R.v42149 (state s) (inputs i) = Zmod.unsigned (N.v42149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42149 s i)) at 1.
  unfold R.v42149, N.v42149.
  rewrite ?node_42146.
  rewrite ?node_42147.
  rewrite ?node_42148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42150 (s : N.State) (i : N.Inputs) :
  R.v42150 (state s) (inputs i) = Zmod.unsigned (N.v42150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42150 s i)) at 1.
  unfold R.v42150, N.v42150.
  rewrite ?node_42145.
  rewrite ?node_42149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42151 (s : N.State) (i : N.Inputs) :
  R.v42151 (state s) (inputs i) = Zmod.unsigned (N.v42151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42151 s i)) at 1.
  unfold R.v42151, N.v42151.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42152 (s : N.State) (i : N.Inputs) :
  R.v42152 (state s) (inputs i) = Zmod.unsigned (N.v42152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42152 s i)) at 1.
  unfold R.v42152, N.v42152.
  rewrite ?node_9613.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42153 (s : N.State) (i : N.Inputs) :
  R.v42153 (state s) (inputs i) = Zmod.unsigned (N.v42153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42153 s i)) at 1.
  unfold R.v42153, N.v42153.
  unfold R.v6, N.v6.
  rewrite ?node_9609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42154 (s : N.State) (i : N.Inputs) :
  R.v42154 (state s) (inputs i) = Zmod.unsigned (N.v42154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42154 s i)) at 1.
  unfold R.v42154, N.v42154.
  unfold R.v6, N.v6.
  rewrite ?node_9606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42155 (s : N.State) (i : N.Inputs) :
  R.v42155 (state s) (inputs i) = Zmod.unsigned (N.v42155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42155 s i)) at 1.
  unfold R.v42155, N.v42155.
  rewrite ?node_42153.
  rewrite ?node_42154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42156 (s : N.State) (i : N.Inputs) :
  R.v42156 (state s) (inputs i) = Zmod.unsigned (N.v42156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42156 s i)) at 1.
  unfold R.v42156, N.v42156.
  unfold R.v16484, N.v16484.
  rewrite ?node_42155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42157 (s : N.State) (i : N.Inputs) :
  R.v42157 (state s) (inputs i) = Zmod.unsigned (N.v42157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42157 s i)) at 1.
  unfold R.v42157, N.v42157.
  rewrite ?node_42152.
  rewrite ?node_42156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42158 (s : N.State) (i : N.Inputs) :
  R.v42158 (state s) (inputs i) = Zmod.unsigned (N.v42158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42158 s i)) at 1.
  unfold R.v42158, N.v42158.
  unfold R.v6, N.v6.
  rewrite ?node_42157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42159 (s : N.State) (i : N.Inputs) :
  R.v42159 (state s) (inputs i) = Zmod.unsigned (N.v42159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42159 s i)) at 1.
  unfold R.v42159, N.v42159.
  rewrite ?node_9614.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42160 (s : N.State) (i : N.Inputs) :
  R.v42160 (state s) (inputs i) = Zmod.unsigned (N.v42160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42160 s i)) at 1.
  unfold R.v42160, N.v42160.
  unfold R.v6, N.v6.
  rewrite ?node_9771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42161 (s : N.State) (i : N.Inputs) :
  R.v42161 (state s) (inputs i) = Zmod.unsigned (N.v42161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42161 s i)) at 1.
  unfold R.v42161, N.v42161.
  rewrite ?node_42159.
  rewrite ?node_42160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42162 (s : N.State) (i : N.Inputs) :
  R.v42162 (state s) (inputs i) = Zmod.unsigned (N.v42162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42162 s i)) at 1.
  unfold R.v42162, N.v42162.
  rewrite ?node_42158.
  rewrite ?node_42161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42163 (s : N.State) (i : N.Inputs) :
  R.v42163 (state s) (inputs i) = Zmod.unsigned (N.v42163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42163 s i)) at 1.
  unfold R.v42163, N.v42163.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42164 (s : N.State) (i : N.Inputs) :
  R.v42164 (state s) (inputs i) = Zmod.unsigned (N.v42164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42164 s i)) at 1.
  unfold R.v42164, N.v42164.
  rewrite ?node_9621.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42165 (s : N.State) (i : N.Inputs) :
  R.v42165 (state s) (inputs i) = Zmod.unsigned (N.v42165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42165 s i)) at 1.
  unfold R.v42165, N.v42165.
  unfold R.v6, N.v6.
  rewrite ?node_9617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42166 (s : N.State) (i : N.Inputs) :
  R.v42166 (state s) (inputs i) = Zmod.unsigned (N.v42166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42166 s i)) at 1.
  unfold R.v42166, N.v42166.
  unfold R.v6, N.v6.
  rewrite ?node_9614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42167 (s : N.State) (i : N.Inputs) :
  R.v42167 (state s) (inputs i) = Zmod.unsigned (N.v42167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42167 s i)) at 1.
  unfold R.v42167, N.v42167.
  rewrite ?node_42165.
  rewrite ?node_42166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42168 (s : N.State) (i : N.Inputs) :
  R.v42168 (state s) (inputs i) = Zmod.unsigned (N.v42168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42168 s i)) at 1.
  unfold R.v42168, N.v42168.
  unfold R.v16484, N.v16484.
  rewrite ?node_42167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42169 (s : N.State) (i : N.Inputs) :
  R.v42169 (state s) (inputs i) = Zmod.unsigned (N.v42169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42169 s i)) at 1.
  unfold R.v42169, N.v42169.
  rewrite ?node_42164.
  rewrite ?node_42168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42170 (s : N.State) (i : N.Inputs) :
  R.v42170 (state s) (inputs i) = Zmod.unsigned (N.v42170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42170 s i)) at 1.
  unfold R.v42170, N.v42170.
  unfold R.v6, N.v6.
  rewrite ?node_42169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42171 (s : N.State) (i : N.Inputs) :
  R.v42171 (state s) (inputs i) = Zmod.unsigned (N.v42171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42171 s i)) at 1.
  unfold R.v42171, N.v42171.
  rewrite ?node_9622.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42172 (s : N.State) (i : N.Inputs) :
  R.v42172 (state s) (inputs i) = Zmod.unsigned (N.v42172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42172 s i)) at 1.
  unfold R.v42172, N.v42172.
  unfold R.v6, N.v6.
  rewrite ?node_9791.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42173 (s : N.State) (i : N.Inputs) :
  R.v42173 (state s) (inputs i) = Zmod.unsigned (N.v42173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42173 s i)) at 1.
  unfold R.v42173, N.v42173.
  rewrite ?node_42171.
  rewrite ?node_42172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42174 (s : N.State) (i : N.Inputs) :
  R.v42174 (state s) (inputs i) = Zmod.unsigned (N.v42174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42174 s i)) at 1.
  unfold R.v42174, N.v42174.
  rewrite ?node_42170.
  rewrite ?node_42173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42175 (s : N.State) (i : N.Inputs) :
  R.v42175 (state s) (inputs i) = Zmod.unsigned (N.v42175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42175 s i)) at 1.
  unfold R.v42175, N.v42175.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42176 (s : N.State) (i : N.Inputs) :
  R.v42176 (state s) (inputs i) = Zmod.unsigned (N.v42176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42176 s i)) at 1.
  unfold R.v42176, N.v42176.
  rewrite ?node_9700.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42177 (s : N.State) (i : N.Inputs) :
  R.v42177 (state s) (inputs i) = Zmod.unsigned (N.v42177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42177 s i)) at 1.
  unfold R.v42177, N.v42177.
  rewrite ?node_9696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42178 (s : N.State) (i : N.Inputs) :
  R.v42178 (state s) (inputs i) = Zmod.unsigned (N.v42178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42178 s i)) at 1.
  unfold R.v42178, N.v42178.
  rewrite ?node_9688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42179 (s : N.State) (i : N.Inputs) :
  R.v42179 (state s) (inputs i) = Zmod.unsigned (N.v42179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42179 s i)) at 1.
  unfold R.v42179, N.v42179.
  unfold R.v6, N.v6.
  rewrite ?node_9680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42180 (s : N.State) (i : N.Inputs) :
  R.v42180 (state s) (inputs i) = Zmod.unsigned (N.v42180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42180 s i)) at 1.
  unfold R.v42180, N.v42180.
  unfold R.v6, N.v6.
  rewrite ?node_9673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42181 (s : N.State) (i : N.Inputs) :
  R.v42181 (state s) (inputs i) = Zmod.unsigned (N.v42181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42181 s i)) at 1.
  unfold R.v42181, N.v42181.
  rewrite ?node_42179.
  rewrite ?node_42180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42182 (s : N.State) (i : N.Inputs) :
  R.v42182 (state s) (inputs i) = Zmod.unsigned (N.v42182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42182 s i)) at 1.
  unfold R.v42182, N.v42182.
  unfold R.v16484, N.v16484.
  rewrite ?node_42181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42183 (s : N.State) (i : N.Inputs) :
  R.v42183 (state s) (inputs i) = Zmod.unsigned (N.v42183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42183 s i)) at 1.
  unfold R.v42183, N.v42183.
  rewrite ?node_42176.
  rewrite ?node_42177.
  rewrite ?node_42178.
  rewrite ?node_42182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42184 (s : N.State) (i : N.Inputs) :
  R.v42184 (state s) (inputs i) = Zmod.unsigned (N.v42184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42184 s i)) at 1.
  unfold R.v42184, N.v42184.
  unfold R.v6, N.v6.
  rewrite ?node_42183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42185 (s : N.State) (i : N.Inputs) :
  R.v42185 (state s) (inputs i) = Zmod.unsigned (N.v42185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42185 s i)) at 1.
  unfold R.v42185, N.v42185.
  rewrite ?node_9701.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42186 (s : N.State) (i : N.Inputs) :
  R.v42186 (state s) (inputs i) = Zmod.unsigned (N.v42186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42186 s i)) at 1.
  unfold R.v42186, N.v42186.
  unfold R.v6, N.v6.
  rewrite ?node_9850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42187 (s : N.State) (i : N.Inputs) :
  R.v42187 (state s) (inputs i) = Zmod.unsigned (N.v42187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42187 s i)) at 1.
  unfold R.v42187, N.v42187.
  unfold R.v6, N.v6.
  rewrite ?node_9932.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42188 (s : N.State) (i : N.Inputs) :
  R.v42188 (state s) (inputs i) = Zmod.unsigned (N.v42188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42188 s i)) at 1.
  unfold R.v42188, N.v42188.
  rewrite ?node_42185.
  rewrite ?node_42186.
  rewrite ?node_42187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42189 (s : N.State) (i : N.Inputs) :
  R.v42189 (state s) (inputs i) = Zmod.unsigned (N.v42189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42189 s i)) at 1.
  unfold R.v42189, N.v42189.
  rewrite ?node_42184.
  rewrite ?node_42188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42190 (s : N.State) (i : N.Inputs) :
  R.v42190 (state s) (inputs i) = Zmod.unsigned (N.v42190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42190 s i)) at 1.
  unfold R.v42190, N.v42190.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42191 (s : N.State) (i : N.Inputs) :
  R.v42191 (state s) (inputs i) = Zmod.unsigned (N.v42191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42191 s i)) at 1.
  unfold R.v42191, N.v42191.
  rewrite ?node_9688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42192 (s : N.State) (i : N.Inputs) :
  R.v42192 (state s) (inputs i) = Zmod.unsigned (N.v42192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42192 s i)) at 1.
  unfold R.v42192, N.v42192.
  unfold R.v6, N.v6.
  rewrite ?node_9680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42193 (s : N.State) (i : N.Inputs) :
  R.v42193 (state s) (inputs i) = Zmod.unsigned (N.v42193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42193 s i)) at 1.
  unfold R.v42193, N.v42193.
  unfold R.v6, N.v6.
  rewrite ?node_9673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42194 (s : N.State) (i : N.Inputs) :
  R.v42194 (state s) (inputs i) = Zmod.unsigned (N.v42194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42194 s i)) at 1.
  unfold R.v42194, N.v42194.
  rewrite ?node_42192.
  rewrite ?node_42193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42195 (s : N.State) (i : N.Inputs) :
  R.v42195 (state s) (inputs i) = Zmod.unsigned (N.v42195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42195 s i)) at 1.
  unfold R.v42195, N.v42195.
  unfold R.v16484, N.v16484.
  rewrite ?node_42194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42196 (s : N.State) (i : N.Inputs) :
  R.v42196 (state s) (inputs i) = Zmod.unsigned (N.v42196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42196 s i)) at 1.
  unfold R.v42196, N.v42196.
  rewrite ?node_42191.
  rewrite ?node_42195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42197 (s : N.State) (i : N.Inputs) :
  R.v42197 (state s) (inputs i) = Zmod.unsigned (N.v42197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42197 s i)) at 1.
  unfold R.v42197, N.v42197.
  unfold R.v6, N.v6.
  rewrite ?node_42196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42198 (s : N.State) (i : N.Inputs) :
  R.v42198 (state s) (inputs i) = Zmod.unsigned (N.v42198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42198 s i)) at 1.
  unfold R.v42198, N.v42198.
  rewrite ?node_9689.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42199 (s : N.State) (i : N.Inputs) :
  R.v42199 (state s) (inputs i) = Zmod.unsigned (N.v42199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42199 s i)) at 1.
  unfold R.v42199, N.v42199.
  unfold R.v6, N.v6.
  rewrite ?node_9850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42200 (s : N.State) (i : N.Inputs) :
  R.v42200 (state s) (inputs i) = Zmod.unsigned (N.v42200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42200 s i)) at 1.
  unfold R.v42200, N.v42200.
  rewrite ?node_42198.
  rewrite ?node_42199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42201 (s : N.State) (i : N.Inputs) :
  R.v42201 (state s) (inputs i) = Zmod.unsigned (N.v42201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42201 s i)) at 1.
  unfold R.v42201, N.v42201.
  rewrite ?node_42197.
  rewrite ?node_42200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42202 (s : N.State) (i : N.Inputs) :
  R.v42202 (state s) (inputs i) = Zmod.unsigned (N.v42202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42202 s i)) at 1.
  unfold R.v42202, N.v42202.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42203 (s : N.State) (i : N.Inputs) :
  R.v42203 (state s) (inputs i) = Zmod.unsigned (N.v42203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42203 s i)) at 1.
  unfold R.v42203, N.v42203.
  rewrite ?node_9700.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42204 (s : N.State) (i : N.Inputs) :
  R.v42204 (state s) (inputs i) = Zmod.unsigned (N.v42204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42204 s i)) at 1.
  unfold R.v42204, N.v42204.
  unfold R.v6, N.v6.
  rewrite ?node_9696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42205 (s : N.State) (i : N.Inputs) :
  R.v42205 (state s) (inputs i) = Zmod.unsigned (N.v42205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42205 s i)) at 1.
  unfold R.v42205, N.v42205.
  unfold R.v6, N.v6.
  rewrite ?node_9689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42206 (s : N.State) (i : N.Inputs) :
  R.v42206 (state s) (inputs i) = Zmod.unsigned (N.v42206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42206 s i)) at 1.
  unfold R.v42206, N.v42206.
  rewrite ?node_42204.
  rewrite ?node_42205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42207 (s : N.State) (i : N.Inputs) :
  R.v42207 (state s) (inputs i) = Zmod.unsigned (N.v42207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42207 s i)) at 1.
  unfold R.v42207, N.v42207.
  unfold R.v16484, N.v16484.
  rewrite ?node_42206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42208 (s : N.State) (i : N.Inputs) :
  R.v42208 (state s) (inputs i) = Zmod.unsigned (N.v42208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42208 s i)) at 1.
  unfold R.v42208, N.v42208.
  rewrite ?node_42203.
  rewrite ?node_42207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42209 (s : N.State) (i : N.Inputs) :
  R.v42209 (state s) (inputs i) = Zmod.unsigned (N.v42209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42209 s i)) at 1.
  unfold R.v42209, N.v42209.
  unfold R.v6, N.v6.
  rewrite ?node_42208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42210 (s : N.State) (i : N.Inputs) :
  R.v42210 (state s) (inputs i) = Zmod.unsigned (N.v42210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42210 s i)) at 1.
  unfold R.v42210, N.v42210.
  rewrite ?node_9701.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42211 (s : N.State) (i : N.Inputs) :
  R.v42211 (state s) (inputs i) = Zmod.unsigned (N.v42211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42211 s i)) at 1.
  unfold R.v42211, N.v42211.
  unfold R.v6, N.v6.
  rewrite ?node_9932.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42212 (s : N.State) (i : N.Inputs) :
  R.v42212 (state s) (inputs i) = Zmod.unsigned (N.v42212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42212 s i)) at 1.
  unfold R.v42212, N.v42212.
  rewrite ?node_42210.
  rewrite ?node_42211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42213 (s : N.State) (i : N.Inputs) :
  R.v42213 (state s) (inputs i) = Zmod.unsigned (N.v42213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42213 s i)) at 1.
  unfold R.v42213, N.v42213.
  rewrite ?node_42209.
  rewrite ?node_42212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42214 (s : N.State) (i : N.Inputs) :
  R.v42214 (state s) (inputs i) = Zmod.unsigned (N.v42214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42214 s i)) at 1.
  unfold R.v42214, N.v42214.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42215 (s : N.State) (i : N.Inputs) :
  R.v42215 (state s) (inputs i) = Zmod.unsigned (N.v42215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42215 s i)) at 1.
  unfold R.v42215, N.v42215.
  rewrite ?node_9731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42216 (s : N.State) (i : N.Inputs) :
  R.v42216 (state s) (inputs i) = Zmod.unsigned (N.v42216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42216 s i)) at 1.
  unfold R.v42216, N.v42216.
  rewrite ?node_9727.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42217 (s : N.State) (i : N.Inputs) :
  R.v42217 (state s) (inputs i) = Zmod.unsigned (N.v42217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42217 s i)) at 1.
  unfold R.v42217, N.v42217.
  rewrite ?node_9723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42218 (s : N.State) (i : N.Inputs) :
  R.v42218 (state s) (inputs i) = Zmod.unsigned (N.v42218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42218 s i)) at 1.
  unfold R.v42218, N.v42218.
  unfold R.v6, N.v6.
  rewrite ?node_9715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42219 (s : N.State) (i : N.Inputs) :
  R.v42219 (state s) (inputs i) = Zmod.unsigned (N.v42219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42219 s i)) at 1.
  unfold R.v42219, N.v42219.
  unfold R.v6, N.v6.
  rewrite ?node_9708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42220 (s : N.State) (i : N.Inputs) :
  R.v42220 (state s) (inputs i) = Zmod.unsigned (N.v42220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42220 s i)) at 1.
  unfold R.v42220, N.v42220.
  rewrite ?node_42218.
  rewrite ?node_42219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42221 (s : N.State) (i : N.Inputs) :
  R.v42221 (state s) (inputs i) = Zmod.unsigned (N.v42221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42221 s i)) at 1.
  unfold R.v42221, N.v42221.
  unfold R.v16484, N.v16484.
  rewrite ?node_42220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42222 (s : N.State) (i : N.Inputs) :
  R.v42222 (state s) (inputs i) = Zmod.unsigned (N.v42222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42222 s i)) at 1.
  unfold R.v42222, N.v42222.
  rewrite ?node_42215.
  rewrite ?node_42216.
  rewrite ?node_42217.
  rewrite ?node_42221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42223 (s : N.State) (i : N.Inputs) :
  R.v42223 (state s) (inputs i) = Zmod.unsigned (N.v42223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42223 s i)) at 1.
  unfold R.v42223, N.v42223.
  unfold R.v6, N.v6.
  rewrite ?node_42222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42224 (s : N.State) (i : N.Inputs) :
  R.v42224 (state s) (inputs i) = Zmod.unsigned (N.v42224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42224 s i)) at 1.
  unfold R.v42224, N.v42224.
  rewrite ?node_9732.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42225 (s : N.State) (i : N.Inputs) :
  R.v42225 (state s) (inputs i) = Zmod.unsigned (N.v42225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42225 s i)) at 1.
  unfold R.v42225, N.v42225.
  unfold R.v6, N.v6.
  rewrite ?node_9885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42226 (s : N.State) (i : N.Inputs) :
  R.v42226 (state s) (inputs i) = Zmod.unsigned (N.v42226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42226 s i)) at 1.
  unfold R.v42226, N.v42226.
  unfold R.v6, N.v6.
  rewrite ?node_9935.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42227 (s : N.State) (i : N.Inputs) :
  R.v42227 (state s) (inputs i) = Zmod.unsigned (N.v42227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42227 s i)) at 1.
  unfold R.v42227, N.v42227.
  rewrite ?node_42224.
  rewrite ?node_42225.
  rewrite ?node_42226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42228 (s : N.State) (i : N.Inputs) :
  R.v42228 (state s) (inputs i) = Zmod.unsigned (N.v42228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42228 s i)) at 1.
  unfold R.v42228, N.v42228.
  rewrite ?node_42223.
  rewrite ?node_42227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42229 (s : N.State) (i : N.Inputs) :
  R.v42229 (state s) (inputs i) = Zmod.unsigned (N.v42229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42229 s i)) at 1.
  unfold R.v42229, N.v42229.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42230 (s : N.State) (i : N.Inputs) :
  R.v42230 (state s) (inputs i) = Zmod.unsigned (N.v42230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42230 s i)) at 1.
  unfold R.v42230, N.v42230.
  rewrite ?node_9723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42231 (s : N.State) (i : N.Inputs) :
  R.v42231 (state s) (inputs i) = Zmod.unsigned (N.v42231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42231 s i)) at 1.
  unfold R.v42231, N.v42231.
  unfold R.v6, N.v6.
  rewrite ?node_9715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42232 (s : N.State) (i : N.Inputs) :
  R.v42232 (state s) (inputs i) = Zmod.unsigned (N.v42232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42232 s i)) at 1.
  unfold R.v42232, N.v42232.
  unfold R.v6, N.v6.
  rewrite ?node_9708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42233 (s : N.State) (i : N.Inputs) :
  R.v42233 (state s) (inputs i) = Zmod.unsigned (N.v42233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42233 s i)) at 1.
  unfold R.v42233, N.v42233.
  rewrite ?node_42231.
  rewrite ?node_42232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42234 (s : N.State) (i : N.Inputs) :
  R.v42234 (state s) (inputs i) = Zmod.unsigned (N.v42234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42234 s i)) at 1.
  unfold R.v42234, N.v42234.
  unfold R.v16484, N.v16484.
  rewrite ?node_42233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42235 (s : N.State) (i : N.Inputs) :
  R.v42235 (state s) (inputs i) = Zmod.unsigned (N.v42235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42235 s i)) at 1.
  unfold R.v42235, N.v42235.
  rewrite ?node_42230.
  rewrite ?node_42234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42236 (s : N.State) (i : N.Inputs) :
  R.v42236 (state s) (inputs i) = Zmod.unsigned (N.v42236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42236 s i)) at 1.
  unfold R.v42236, N.v42236.
  unfold R.v6, N.v6.
  rewrite ?node_42235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42237 (s : N.State) (i : N.Inputs) :
  R.v42237 (state s) (inputs i) = Zmod.unsigned (N.v42237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42237 s i)) at 1.
  unfold R.v42237, N.v42237.
  rewrite ?node_9724.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42238 (s : N.State) (i : N.Inputs) :
  R.v42238 (state s) (inputs i) = Zmod.unsigned (N.v42238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42238 s i)) at 1.
  unfold R.v42238, N.v42238.
  unfold R.v6, N.v6.
  rewrite ?node_9885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42239 (s : N.State) (i : N.Inputs) :
  R.v42239 (state s) (inputs i) = Zmod.unsigned (N.v42239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42239 s i)) at 1.
  unfold R.v42239, N.v42239.
  rewrite ?node_42237.
  rewrite ?node_42238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42240 (s : N.State) (i : N.Inputs) :
  R.v42240 (state s) (inputs i) = Zmod.unsigned (N.v42240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42240 s i)) at 1.
  unfold R.v42240, N.v42240.
  rewrite ?node_42236.
  rewrite ?node_42239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42241 (s : N.State) (i : N.Inputs) :
  R.v42241 (state s) (inputs i) = Zmod.unsigned (N.v42241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42241 s i)) at 1.
  unfold R.v42241, N.v42241.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42242 (s : N.State) (i : N.Inputs) :
  R.v42242 (state s) (inputs i) = Zmod.unsigned (N.v42242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42242 s i)) at 1.
  unfold R.v42242, N.v42242.
  rewrite ?node_9731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42243 (s : N.State) (i : N.Inputs) :
  R.v42243 (state s) (inputs i) = Zmod.unsigned (N.v42243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42243 s i)) at 1.
  unfold R.v42243, N.v42243.
  unfold R.v6, N.v6.
  rewrite ?node_9727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42244 (s : N.State) (i : N.Inputs) :
  R.v42244 (state s) (inputs i) = Zmod.unsigned (N.v42244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42244 s i)) at 1.
  unfold R.v42244, N.v42244.
  unfold R.v6, N.v6.
  rewrite ?node_9724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42245 (s : N.State) (i : N.Inputs) :
  R.v42245 (state s) (inputs i) = Zmod.unsigned (N.v42245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42245 s i)) at 1.
  unfold R.v42245, N.v42245.
  rewrite ?node_42243.
  rewrite ?node_42244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42246 (s : N.State) (i : N.Inputs) :
  R.v42246 (state s) (inputs i) = Zmod.unsigned (N.v42246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42246 s i)) at 1.
  unfold R.v42246, N.v42246.
  unfold R.v16484, N.v16484.
  rewrite ?node_42245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42247 (s : N.State) (i : N.Inputs) :
  R.v42247 (state s) (inputs i) = Zmod.unsigned (N.v42247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42247 s i)) at 1.
  unfold R.v42247, N.v42247.
  rewrite ?node_42242.
  rewrite ?node_42246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42248 (s : N.State) (i : N.Inputs) :
  R.v42248 (state s) (inputs i) = Zmod.unsigned (N.v42248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42248 s i)) at 1.
  unfold R.v42248, N.v42248.
  unfold R.v6, N.v6.
  rewrite ?node_42247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42249 (s : N.State) (i : N.Inputs) :
  R.v42249 (state s) (inputs i) = Zmod.unsigned (N.v42249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42249 s i)) at 1.
  unfold R.v42249, N.v42249.
  rewrite ?node_9732.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42250 (s : N.State) (i : N.Inputs) :
  R.v42250 (state s) (inputs i) = Zmod.unsigned (N.v42250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42250 s i)) at 1.
  unfold R.v42250, N.v42250.
  unfold R.v6, N.v6.
  rewrite ?node_9935.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42251 (s : N.State) (i : N.Inputs) :
  R.v42251 (state s) (inputs i) = Zmod.unsigned (N.v42251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42251 s i)) at 1.
  unfold R.v42251, N.v42251.
  rewrite ?node_42249.
  rewrite ?node_42250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42252 (s : N.State) (i : N.Inputs) :
  R.v42252 (state s) (inputs i) = Zmod.unsigned (N.v42252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42252 s i)) at 1.
  unfold R.v42252, N.v42252.
  rewrite ?node_42248.
  rewrite ?node_42251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42253 (s : N.State) (i : N.Inputs) :
  R.v42253 (state s) (inputs i) = Zmod.unsigned (N.v42253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42253 s i)) at 1.
  unfold R.v42253, N.v42253.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42254 (s : N.State) (i : N.Inputs) :
  R.v42254 (state s) (inputs i) = Zmod.unsigned (N.v42254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42254 s i)) at 1.
  unfold R.v42254, N.v42254.
  rewrite ?node_9751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42255 (s : N.State) (i : N.Inputs) :
  R.v42255 (state s) (inputs i) = Zmod.unsigned (N.v42255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42255 s i)) at 1.
  unfold R.v42255, N.v42255.
  rewrite ?node_9747.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42256 (s : N.State) (i : N.Inputs) :
  R.v42256 (state s) (inputs i) = Zmod.unsigned (N.v42256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42256 s i)) at 1.
  unfold R.v42256, N.v42256.
  rewrite ?node_9743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42257 (s : N.State) (i : N.Inputs) :
  R.v42257 (state s) (inputs i) = Zmod.unsigned (N.v42257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42257 s i)) at 1.
  unfold R.v42257, N.v42257.
  unfold R.v6, N.v6.
  rewrite ?node_9739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42258 (s : N.State) (i : N.Inputs) :
  R.v42258 (state s) (inputs i) = Zmod.unsigned (N.v42258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42258 s i)) at 1.
  unfold R.v42258, N.v42258.
  unfold R.v6, N.v6.
  rewrite ?node_9736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42259 (s : N.State) (i : N.Inputs) :
  R.v42259 (state s) (inputs i) = Zmod.unsigned (N.v42259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42259 s i)) at 1.
  unfold R.v42259, N.v42259.
  rewrite ?node_42257.
  rewrite ?node_42258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42260 (s : N.State) (i : N.Inputs) :
  R.v42260 (state s) (inputs i) = Zmod.unsigned (N.v42260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42260 s i)) at 1.
  unfold R.v42260, N.v42260.
  unfold R.v16484, N.v16484.
  rewrite ?node_42259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42261 (s : N.State) (i : N.Inputs) :
  R.v42261 (state s) (inputs i) = Zmod.unsigned (N.v42261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42261 s i)) at 1.
  unfold R.v42261, N.v42261.
  rewrite ?node_42254.
  rewrite ?node_42255.
  rewrite ?node_42256.
  rewrite ?node_42260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42262 (s : N.State) (i : N.Inputs) :
  R.v42262 (state s) (inputs i) = Zmod.unsigned (N.v42262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42262 s i)) at 1.
  unfold R.v42262, N.v42262.
  unfold R.v6, N.v6.
  rewrite ?node_42261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42263 (s : N.State) (i : N.Inputs) :
  R.v42263 (state s) (inputs i) = Zmod.unsigned (N.v42263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42263 s i)) at 1.
  unfold R.v42263, N.v42263.
  rewrite ?node_9752.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42264 (s : N.State) (i : N.Inputs) :
  R.v42264 (state s) (inputs i) = Zmod.unsigned (N.v42264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42264 s i)) at 1.
  unfold R.v42264, N.v42264.
  unfold R.v6, N.v6.
  rewrite ?node_9905.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42265 (s : N.State) (i : N.Inputs) :
  R.v42265 (state s) (inputs i) = Zmod.unsigned (N.v42265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42265 s i)) at 1.
  unfold R.v42265, N.v42265.
  unfold R.v6, N.v6.
  rewrite ?node_9939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42266 (s : N.State) (i : N.Inputs) :
  R.v42266 (state s) (inputs i) = Zmod.unsigned (N.v42266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42266 s i)) at 1.
  unfold R.v42266, N.v42266.
  rewrite ?node_42263.
  rewrite ?node_42264.
  rewrite ?node_42265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42267 (s : N.State) (i : N.Inputs) :
  R.v42267 (state s) (inputs i) = Zmod.unsigned (N.v42267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42267 s i)) at 1.
  unfold R.v42267, N.v42267.
  rewrite ?node_42262.
  rewrite ?node_42266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42268 (s : N.State) (i : N.Inputs) :
  R.v42268 (state s) (inputs i) = Zmod.unsigned (N.v42268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42268 s i)) at 1.
  unfold R.v42268, N.v42268.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42269 (s : N.State) (i : N.Inputs) :
  R.v42269 (state s) (inputs i) = Zmod.unsigned (N.v42269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42269 s i)) at 1.
  unfold R.v42269, N.v42269.
  rewrite ?node_9743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42270 (s : N.State) (i : N.Inputs) :
  R.v42270 (state s) (inputs i) = Zmod.unsigned (N.v42270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42270 s i)) at 1.
  unfold R.v42270, N.v42270.
  unfold R.v6, N.v6.
  rewrite ?node_9739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42271 (s : N.State) (i : N.Inputs) :
  R.v42271 (state s) (inputs i) = Zmod.unsigned (N.v42271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42271 s i)) at 1.
  unfold R.v42271, N.v42271.
  unfold R.v6, N.v6.
  rewrite ?node_9736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42272 (s : N.State) (i : N.Inputs) :
  R.v42272 (state s) (inputs i) = Zmod.unsigned (N.v42272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42272 s i)) at 1.
  unfold R.v42272, N.v42272.
  rewrite ?node_42270.
  rewrite ?node_42271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42273 (s : N.State) (i : N.Inputs) :
  R.v42273 (state s) (inputs i) = Zmod.unsigned (N.v42273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42273 s i)) at 1.
  unfold R.v42273, N.v42273.
  unfold R.v16484, N.v16484.
  rewrite ?node_42272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42274 (s : N.State) (i : N.Inputs) :
  R.v42274 (state s) (inputs i) = Zmod.unsigned (N.v42274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42274 s i)) at 1.
  unfold R.v42274, N.v42274.
  rewrite ?node_42269.
  rewrite ?node_42273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42275 (s : N.State) (i : N.Inputs) :
  R.v42275 (state s) (inputs i) = Zmod.unsigned (N.v42275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42275 s i)) at 1.
  unfold R.v42275, N.v42275.
  unfold R.v6, N.v6.
  rewrite ?node_42274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42276 (s : N.State) (i : N.Inputs) :
  R.v42276 (state s) (inputs i) = Zmod.unsigned (N.v42276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42276 s i)) at 1.
  unfold R.v42276, N.v42276.
  rewrite ?node_9744.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42277 (s : N.State) (i : N.Inputs) :
  R.v42277 (state s) (inputs i) = Zmod.unsigned (N.v42277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42277 s i)) at 1.
  unfold R.v42277, N.v42277.
  unfold R.v6, N.v6.
  rewrite ?node_9905.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42278 (s : N.State) (i : N.Inputs) :
  R.v42278 (state s) (inputs i) = Zmod.unsigned (N.v42278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42278 s i)) at 1.
  unfold R.v42278, N.v42278.
  rewrite ?node_42276.
  rewrite ?node_42277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42279 (s : N.State) (i : N.Inputs) :
  R.v42279 (state s) (inputs i) = Zmod.unsigned (N.v42279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42279 s i)) at 1.
  unfold R.v42279, N.v42279.
  rewrite ?node_42275.
  rewrite ?node_42278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42280 (s : N.State) (i : N.Inputs) :
  R.v42280 (state s) (inputs i) = Zmod.unsigned (N.v42280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42280 s i)) at 1.
  unfold R.v42280, N.v42280.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42281 (s : N.State) (i : N.Inputs) :
  R.v42281 (state s) (inputs i) = Zmod.unsigned (N.v42281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42281 s i)) at 1.
  unfold R.v42281, N.v42281.
  rewrite ?node_9751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42282 (s : N.State) (i : N.Inputs) :
  R.v42282 (state s) (inputs i) = Zmod.unsigned (N.v42282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42282 s i)) at 1.
  unfold R.v42282, N.v42282.
  unfold R.v6, N.v6.
  rewrite ?node_9747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42283 (s : N.State) (i : N.Inputs) :
  R.v42283 (state s) (inputs i) = Zmod.unsigned (N.v42283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42283 s i)) at 1.
  unfold R.v42283, N.v42283.
  unfold R.v6, N.v6.
  rewrite ?node_9744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42284 (s : N.State) (i : N.Inputs) :
  R.v42284 (state s) (inputs i) = Zmod.unsigned (N.v42284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42284 s i)) at 1.
  unfold R.v42284, N.v42284.
  rewrite ?node_42282.
  rewrite ?node_42283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42285 (s : N.State) (i : N.Inputs) :
  R.v42285 (state s) (inputs i) = Zmod.unsigned (N.v42285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42285 s i)) at 1.
  unfold R.v42285, N.v42285.
  unfold R.v16484, N.v16484.
  rewrite ?node_42284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42286 (s : N.State) (i : N.Inputs) :
  R.v42286 (state s) (inputs i) = Zmod.unsigned (N.v42286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42286 s i)) at 1.
  unfold R.v42286, N.v42286.
  rewrite ?node_42281.
  rewrite ?node_42285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42287 (s : N.State) (i : N.Inputs) :
  R.v42287 (state s) (inputs i) = Zmod.unsigned (N.v42287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42287 s i)) at 1.
  unfold R.v42287, N.v42287.
  unfold R.v6, N.v6.
  rewrite ?node_42286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42288 (s : N.State) (i : N.Inputs) :
  R.v42288 (state s) (inputs i) = Zmod.unsigned (N.v42288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42288 s i)) at 1.
  unfold R.v42288, N.v42288.
  rewrite ?node_9752.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42289 (s : N.State) (i : N.Inputs) :
  R.v42289 (state s) (inputs i) = Zmod.unsigned (N.v42289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42289 s i)) at 1.
  unfold R.v42289, N.v42289.
  unfold R.v6, N.v6.
  rewrite ?node_9939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42290 (s : N.State) (i : N.Inputs) :
  R.v42290 (state s) (inputs i) = Zmod.unsigned (N.v42290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42290 s i)) at 1.
  unfold R.v42290, N.v42290.
  rewrite ?node_42288.
  rewrite ?node_42289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42291 (s : N.State) (i : N.Inputs) :
  R.v42291 (state s) (inputs i) = Zmod.unsigned (N.v42291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42291 s i)) at 1.
  unfold R.v42291, N.v42291.
  rewrite ?node_42287.
  rewrite ?node_42290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42292 (s : N.State) (i : N.Inputs) :
  R.v42292 (state s) (inputs i) = Zmod.unsigned (N.v42292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42292 s i)) at 1.
  unfold R.v42292, N.v42292.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42293 (s : N.State) (i : N.Inputs) :
  R.v42293 (state s) (inputs i) = Zmod.unsigned (N.v42293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42293 s i)) at 1.
  unfold R.v42293, N.v42293.
  rewrite ?node_9771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42294 (s : N.State) (i : N.Inputs) :
  R.v42294 (state s) (inputs i) = Zmod.unsigned (N.v42294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42294 s i)) at 1.
  unfold R.v42294, N.v42294.
  rewrite ?node_9767.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42295 (s : N.State) (i : N.Inputs) :
  R.v42295 (state s) (inputs i) = Zmod.unsigned (N.v42295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42295 s i)) at 1.
  unfold R.v42295, N.v42295.
  rewrite ?node_9763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42296 (s : N.State) (i : N.Inputs) :
  R.v42296 (state s) (inputs i) = Zmod.unsigned (N.v42296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42296 s i)) at 1.
  unfold R.v42296, N.v42296.
  unfold R.v6, N.v6.
  rewrite ?node_9759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42297 (s : N.State) (i : N.Inputs) :
  R.v42297 (state s) (inputs i) = Zmod.unsigned (N.v42297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42297 s i)) at 1.
  unfold R.v42297, N.v42297.
  unfold R.v6, N.v6.
  rewrite ?node_9756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42298 (s : N.State) (i : N.Inputs) :
  R.v42298 (state s) (inputs i) = Zmod.unsigned (N.v42298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42298 s i)) at 1.
  unfold R.v42298, N.v42298.
  rewrite ?node_42296.
  rewrite ?node_42297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42299 (s : N.State) (i : N.Inputs) :
  R.v42299 (state s) (inputs i) = Zmod.unsigned (N.v42299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42299 s i)) at 1.
  unfold R.v42299, N.v42299.
  unfold R.v16484, N.v16484.
  rewrite ?node_42298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42300 (s : N.State) (i : N.Inputs) :
  R.v42300 (state s) (inputs i) = Zmod.unsigned (N.v42300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42300 s i)) at 1.
  unfold R.v42300, N.v42300.
  rewrite ?node_42293.
  rewrite ?node_42294.
  rewrite ?node_42295.
  rewrite ?node_42299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42301 (s : N.State) (i : N.Inputs) :
  R.v42301 (state s) (inputs i) = Zmod.unsigned (N.v42301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42301 s i)) at 1.
  unfold R.v42301, N.v42301.
  unfold R.v6, N.v6.
  rewrite ?node_42300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42302 (s : N.State) (i : N.Inputs) :
  R.v42302 (state s) (inputs i) = Zmod.unsigned (N.v42302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42302 s i)) at 1.
  unfold R.v42302, N.v42302.
  rewrite ?node_9772.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42303 (s : N.State) (i : N.Inputs) :
  R.v42303 (state s) (inputs i) = Zmod.unsigned (N.v42303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42303 s i)) at 1.
  unfold R.v42303, N.v42303.
  unfold R.v6, N.v6.
  rewrite ?node_9923.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42304 (s : N.State) (i : N.Inputs) :
  R.v42304 (state s) (inputs i) = Zmod.unsigned (N.v42304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42304 s i)) at 1.
  unfold R.v42304, N.v42304.
  unfold R.v6, N.v6.
  rewrite ?node_9943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42305 (s : N.State) (i : N.Inputs) :
  R.v42305 (state s) (inputs i) = Zmod.unsigned (N.v42305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42305 s i)) at 1.
  unfold R.v42305, N.v42305.
  rewrite ?node_42302.
  rewrite ?node_42303.
  rewrite ?node_42304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42306 (s : N.State) (i : N.Inputs) :
  R.v42306 (state s) (inputs i) = Zmod.unsigned (N.v42306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42306 s i)) at 1.
  unfold R.v42306, N.v42306.
  rewrite ?node_42301.
  rewrite ?node_42305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42307 (s : N.State) (i : N.Inputs) :
  R.v42307 (state s) (inputs i) = Zmod.unsigned (N.v42307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42307 s i)) at 1.
  unfold R.v42307, N.v42307.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42308 (s : N.State) (i : N.Inputs) :
  R.v42308 (state s) (inputs i) = Zmod.unsigned (N.v42308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42308 s i)) at 1.
  unfold R.v42308, N.v42308.
  rewrite ?node_9763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42309 (s : N.State) (i : N.Inputs) :
  R.v42309 (state s) (inputs i) = Zmod.unsigned (N.v42309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42309 s i)) at 1.
  unfold R.v42309, N.v42309.
  unfold R.v6, N.v6.
  rewrite ?node_9759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42310 (s : N.State) (i : N.Inputs) :
  R.v42310 (state s) (inputs i) = Zmod.unsigned (N.v42310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42310 s i)) at 1.
  unfold R.v42310, N.v42310.
  unfold R.v6, N.v6.
  rewrite ?node_9756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42311 (s : N.State) (i : N.Inputs) :
  R.v42311 (state s) (inputs i) = Zmod.unsigned (N.v42311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42311 s i)) at 1.
  unfold R.v42311, N.v42311.
  rewrite ?node_42309.
  rewrite ?node_42310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42312 (s : N.State) (i : N.Inputs) :
  R.v42312 (state s) (inputs i) = Zmod.unsigned (N.v42312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42312 s i)) at 1.
  unfold R.v42312, N.v42312.
  unfold R.v16484, N.v16484.
  rewrite ?node_42311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42313 (s : N.State) (i : N.Inputs) :
  R.v42313 (state s) (inputs i) = Zmod.unsigned (N.v42313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42313 s i)) at 1.
  unfold R.v42313, N.v42313.
  rewrite ?node_42308.
  rewrite ?node_42312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42314 (s : N.State) (i : N.Inputs) :
  R.v42314 (state s) (inputs i) = Zmod.unsigned (N.v42314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42314 s i)) at 1.
  unfold R.v42314, N.v42314.
  unfold R.v6, N.v6.
  rewrite ?node_42313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42315 (s : N.State) (i : N.Inputs) :
  R.v42315 (state s) (inputs i) = Zmod.unsigned (N.v42315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42315 s i)) at 1.
  unfold R.v42315, N.v42315.
  rewrite ?node_9764.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42316 (s : N.State) (i : N.Inputs) :
  R.v42316 (state s) (inputs i) = Zmod.unsigned (N.v42316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42316 s i)) at 1.
  unfold R.v42316, N.v42316.
  unfold R.v6, N.v6.
  rewrite ?node_9923.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42317 (s : N.State) (i : N.Inputs) :
  R.v42317 (state s) (inputs i) = Zmod.unsigned (N.v42317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42317 s i)) at 1.
  unfold R.v42317, N.v42317.
  rewrite ?node_42315.
  rewrite ?node_42316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42318 (s : N.State) (i : N.Inputs) :
  R.v42318 (state s) (inputs i) = Zmod.unsigned (N.v42318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42318 s i)) at 1.
  unfold R.v42318, N.v42318.
  rewrite ?node_42314.
  rewrite ?node_42317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42319 (s : N.State) (i : N.Inputs) :
  R.v42319 (state s) (inputs i) = Zmod.unsigned (N.v42319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42319 s i)) at 1.
  unfold R.v42319, N.v42319.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42320 (s : N.State) (i : N.Inputs) :
  R.v42320 (state s) (inputs i) = Zmod.unsigned (N.v42320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42320 s i)) at 1.
  unfold R.v42320, N.v42320.
  rewrite ?node_9771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42321 (s : N.State) (i : N.Inputs) :
  R.v42321 (state s) (inputs i) = Zmod.unsigned (N.v42321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42321 s i)) at 1.
  unfold R.v42321, N.v42321.
  unfold R.v6, N.v6.
  rewrite ?node_9767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42322 (s : N.State) (i : N.Inputs) :
  R.v42322 (state s) (inputs i) = Zmod.unsigned (N.v42322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42322 s i)) at 1.
  unfold R.v42322, N.v42322.
  unfold R.v6, N.v6.
  rewrite ?node_9764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42323 (s : N.State) (i : N.Inputs) :
  R.v42323 (state s) (inputs i) = Zmod.unsigned (N.v42323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42323 s i)) at 1.
  unfold R.v42323, N.v42323.
  rewrite ?node_42321.
  rewrite ?node_42322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42324 (s : N.State) (i : N.Inputs) :
  R.v42324 (state s) (inputs i) = Zmod.unsigned (N.v42324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42324 s i)) at 1.
  unfold R.v42324, N.v42324.
  unfold R.v16484, N.v16484.
  rewrite ?node_42323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42325 (s : N.State) (i : N.Inputs) :
  R.v42325 (state s) (inputs i) = Zmod.unsigned (N.v42325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42325 s i)) at 1.
  unfold R.v42325, N.v42325.
  rewrite ?node_42320.
  rewrite ?node_42324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42326 (s : N.State) (i : N.Inputs) :
  R.v42326 (state s) (inputs i) = Zmod.unsigned (N.v42326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42326 s i)) at 1.
  unfold R.v42326, N.v42326.
  unfold R.v6, N.v6.
  rewrite ?node_42325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42327 (s : N.State) (i : N.Inputs) :
  R.v42327 (state s) (inputs i) = Zmod.unsigned (N.v42327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42327 s i)) at 1.
  unfold R.v42327, N.v42327.
  rewrite ?node_9772.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42328 (s : N.State) (i : N.Inputs) :
  R.v42328 (state s) (inputs i) = Zmod.unsigned (N.v42328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42328 s i)) at 1.
  unfold R.v42328, N.v42328.
  unfold R.v6, N.v6.
  rewrite ?node_9943.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42329 (s : N.State) (i : N.Inputs) :
  R.v42329 (state s) (inputs i) = Zmod.unsigned (N.v42329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42329 s i)) at 1.
  unfold R.v42329, N.v42329.
  rewrite ?node_42327.
  rewrite ?node_42328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42330 (s : N.State) (i : N.Inputs) :
  R.v42330 (state s) (inputs i) = Zmod.unsigned (N.v42330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42330 s i)) at 1.
  unfold R.v42330, N.v42330.
  rewrite ?node_42326.
  rewrite ?node_42329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42331 (s : N.State) (i : N.Inputs) :
  R.v42331 (state s) (inputs i) = Zmod.unsigned (N.v42331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42331 s i)) at 1.
  unfold R.v42331, N.v42331.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42332 (s : N.State) (i : N.Inputs) :
  R.v42332 (state s) (inputs i) = Zmod.unsigned (N.v42332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42332 s i)) at 1.
  unfold R.v42332, N.v42332.
  rewrite ?node_9850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42333 (s : N.State) (i : N.Inputs) :
  R.v42333 (state s) (inputs i) = Zmod.unsigned (N.v42333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42333 s i)) at 1.
  unfold R.v42333, N.v42333.
  rewrite ?node_9846.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42334 (s : N.State) (i : N.Inputs) :
  R.v42334 (state s) (inputs i) = Zmod.unsigned (N.v42334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42334 s i)) at 1.
  unfold R.v42334, N.v42334.
  rewrite ?node_9838.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42335 (s : N.State) (i : N.Inputs) :
  R.v42335 (state s) (inputs i) = Zmod.unsigned (N.v42335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42335 s i)) at 1.
  unfold R.v42335, N.v42335.
  unfold R.v6, N.v6.
  rewrite ?node_9830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42336 (s : N.State) (i : N.Inputs) :
  R.v42336 (state s) (inputs i) = Zmod.unsigned (N.v42336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42336 s i)) at 1.
  unfold R.v42336, N.v42336.
  unfold R.v6, N.v6.
  rewrite ?node_9823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42337 (s : N.State) (i : N.Inputs) :
  R.v42337 (state s) (inputs i) = Zmod.unsigned (N.v42337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42337 s i)) at 1.
  unfold R.v42337, N.v42337.
  rewrite ?node_42335.
  rewrite ?node_42336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42338 (s : N.State) (i : N.Inputs) :
  R.v42338 (state s) (inputs i) = Zmod.unsigned (N.v42338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42338 s i)) at 1.
  unfold R.v42338, N.v42338.
  unfold R.v16484, N.v16484.
  rewrite ?node_42337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42339 (s : N.State) (i : N.Inputs) :
  R.v42339 (state s) (inputs i) = Zmod.unsigned (N.v42339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42339 s i)) at 1.
  unfold R.v42339, N.v42339.
  rewrite ?node_42332.
  rewrite ?node_42333.
  rewrite ?node_42334.
  rewrite ?node_42338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42340 (s : N.State) (i : N.Inputs) :
  R.v42340 (state s) (inputs i) = Zmod.unsigned (N.v42340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42340 s i)) at 1.
  unfold R.v42340, N.v42340.
  unfold R.v6, N.v6.
  rewrite ?node_42339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42341 (s : N.State) (i : N.Inputs) :
  R.v42341 (state s) (inputs i) = Zmod.unsigned (N.v42341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42341 s i)) at 1.
  unfold R.v42341, N.v42341.
  rewrite ?node_9851.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42342 (s : N.State) (i : N.Inputs) :
  R.v42342 (state s) (inputs i) = Zmod.unsigned (N.v42342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42342 s i)) at 1.
  unfold R.v42342, N.v42342.
  unfold R.v6, N.v6.
  rewrite ?node_10002.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42343 (s : N.State) (i : N.Inputs) :
  R.v42343 (state s) (inputs i) = Zmod.unsigned (N.v42343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42343 s i)) at 1.
  unfold R.v42343, N.v42343.
  unfold R.v6, N.v6.
  rewrite ?node_10086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42344 (s : N.State) (i : N.Inputs) :
  R.v42344 (state s) (inputs i) = Zmod.unsigned (N.v42344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42344 s i)) at 1.
  unfold R.v42344, N.v42344.
  rewrite ?node_42341.
  rewrite ?node_42342.
  rewrite ?node_42343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42345 (s : N.State) (i : N.Inputs) :
  R.v42345 (state s) (inputs i) = Zmod.unsigned (N.v42345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42345 s i)) at 1.
  unfold R.v42345, N.v42345.
  rewrite ?node_42340.
  rewrite ?node_42344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42346 (s : N.State) (i : N.Inputs) :
  R.v42346 (state s) (inputs i) = Zmod.unsigned (N.v42346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42346 s i)) at 1.
  unfold R.v42346, N.v42346.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42347 (s : N.State) (i : N.Inputs) :
  R.v42347 (state s) (inputs i) = Zmod.unsigned (N.v42347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42347 s i)) at 1.
  unfold R.v42347, N.v42347.
  rewrite ?node_9838.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42348 (s : N.State) (i : N.Inputs) :
  R.v42348 (state s) (inputs i) = Zmod.unsigned (N.v42348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42348 s i)) at 1.
  unfold R.v42348, N.v42348.
  unfold R.v6, N.v6.
  rewrite ?node_9830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42349 (s : N.State) (i : N.Inputs) :
  R.v42349 (state s) (inputs i) = Zmod.unsigned (N.v42349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42349 s i)) at 1.
  unfold R.v42349, N.v42349.
  unfold R.v6, N.v6.
  rewrite ?node_9823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42350 (s : N.State) (i : N.Inputs) :
  R.v42350 (state s) (inputs i) = Zmod.unsigned (N.v42350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42350 s i)) at 1.
  unfold R.v42350, N.v42350.
  rewrite ?node_42348.
  rewrite ?node_42349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42351 (s : N.State) (i : N.Inputs) :
  R.v42351 (state s) (inputs i) = Zmod.unsigned (N.v42351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42351 s i)) at 1.
  unfold R.v42351, N.v42351.
  unfold R.v16484, N.v16484.
  rewrite ?node_42350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42352 (s : N.State) (i : N.Inputs) :
  R.v42352 (state s) (inputs i) = Zmod.unsigned (N.v42352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42352 s i)) at 1.
  unfold R.v42352, N.v42352.
  rewrite ?node_42347.
  rewrite ?node_42351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42353 (s : N.State) (i : N.Inputs) :
  R.v42353 (state s) (inputs i) = Zmod.unsigned (N.v42353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42353 s i)) at 1.
  unfold R.v42353, N.v42353.
  unfold R.v6, N.v6.
  rewrite ?node_42352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42354 (s : N.State) (i : N.Inputs) :
  R.v42354 (state s) (inputs i) = Zmod.unsigned (N.v42354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42354 s i)) at 1.
  unfold R.v42354, N.v42354.
  rewrite ?node_9839.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42355 (s : N.State) (i : N.Inputs) :
  R.v42355 (state s) (inputs i) = Zmod.unsigned (N.v42355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42355 s i)) at 1.
  unfold R.v42355, N.v42355.
  unfold R.v6, N.v6.
  rewrite ?node_10002.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42356 (s : N.State) (i : N.Inputs) :
  R.v42356 (state s) (inputs i) = Zmod.unsigned (N.v42356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42356 s i)) at 1.
  unfold R.v42356, N.v42356.
  rewrite ?node_42354.
  rewrite ?node_42355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42357 (s : N.State) (i : N.Inputs) :
  R.v42357 (state s) (inputs i) = Zmod.unsigned (N.v42357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42357 s i)) at 1.
  unfold R.v42357, N.v42357.
  rewrite ?node_42353.
  rewrite ?node_42356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42358 (s : N.State) (i : N.Inputs) :
  R.v42358 (state s) (inputs i) = Zmod.unsigned (N.v42358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42358 s i)) at 1.
  unfold R.v42358, N.v42358.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42359 (s : N.State) (i : N.Inputs) :
  R.v42359 (state s) (inputs i) = Zmod.unsigned (N.v42359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42359 s i)) at 1.
  unfold R.v42359, N.v42359.
  rewrite ?node_9850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42360 (s : N.State) (i : N.Inputs) :
  R.v42360 (state s) (inputs i) = Zmod.unsigned (N.v42360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42360 s i)) at 1.
  unfold R.v42360, N.v42360.
  unfold R.v6, N.v6.
  rewrite ?node_9846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42361 (s : N.State) (i : N.Inputs) :
  R.v42361 (state s) (inputs i) = Zmod.unsigned (N.v42361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42361 s i)) at 1.
  unfold R.v42361, N.v42361.
  unfold R.v6, N.v6.
  rewrite ?node_9839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42362 (s : N.State) (i : N.Inputs) :
  R.v42362 (state s) (inputs i) = Zmod.unsigned (N.v42362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42362 s i)) at 1.
  unfold R.v42362, N.v42362.
  rewrite ?node_42360.
  rewrite ?node_42361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42363 (s : N.State) (i : N.Inputs) :
  R.v42363 (state s) (inputs i) = Zmod.unsigned (N.v42363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42363 s i)) at 1.
  unfold R.v42363, N.v42363.
  unfold R.v16484, N.v16484.
  rewrite ?node_42362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42364 (s : N.State) (i : N.Inputs) :
  R.v42364 (state s) (inputs i) = Zmod.unsigned (N.v42364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42364 s i)) at 1.
  unfold R.v42364, N.v42364.
  rewrite ?node_42359.
  rewrite ?node_42363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42365 (s : N.State) (i : N.Inputs) :
  R.v42365 (state s) (inputs i) = Zmod.unsigned (N.v42365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42365 s i)) at 1.
  unfold R.v42365, N.v42365.
  unfold R.v6, N.v6.
  rewrite ?node_42364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42366 (s : N.State) (i : N.Inputs) :
  R.v42366 (state s) (inputs i) = Zmod.unsigned (N.v42366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42366 s i)) at 1.
  unfold R.v42366, N.v42366.
  rewrite ?node_9851.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42367 (s : N.State) (i : N.Inputs) :
  R.v42367 (state s) (inputs i) = Zmod.unsigned (N.v42367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42367 s i)) at 1.
  unfold R.v42367, N.v42367.
  unfold R.v6, N.v6.
  rewrite ?node_10086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42368 (s : N.State) (i : N.Inputs) :
  R.v42368 (state s) (inputs i) = Zmod.unsigned (N.v42368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42368 s i)) at 1.
  unfold R.v42368, N.v42368.
  rewrite ?node_42366.
  rewrite ?node_42367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42369 (s : N.State) (i : N.Inputs) :
  R.v42369 (state s) (inputs i) = Zmod.unsigned (N.v42369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42369 s i)) at 1.
  unfold R.v42369, N.v42369.
  rewrite ?node_42365.
  rewrite ?node_42368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42370 (s : N.State) (i : N.Inputs) :
  R.v42370 (state s) (inputs i) = Zmod.unsigned (N.v42370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42370 s i)) at 1.
  unfold R.v42370, N.v42370.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42371 (s : N.State) (i : N.Inputs) :
  R.v42371 (state s) (inputs i) = Zmod.unsigned (N.v42371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42371 s i)) at 1.
  unfold R.v42371, N.v42371.
  rewrite ?node_9885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42372 (s : N.State) (i : N.Inputs) :
  R.v42372 (state s) (inputs i) = Zmod.unsigned (N.v42372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42372 s i)) at 1.
  unfold R.v42372, N.v42372.
  rewrite ?node_9881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42373 (s : N.State) (i : N.Inputs) :
  R.v42373 (state s) (inputs i) = Zmod.unsigned (N.v42373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42373 s i)) at 1.
  unfold R.v42373, N.v42373.
  rewrite ?node_9873.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42374 (s : N.State) (i : N.Inputs) :
  R.v42374 (state s) (inputs i) = Zmod.unsigned (N.v42374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42374 s i)) at 1.
  unfold R.v42374, N.v42374.
  unfold R.v6, N.v6.
  rewrite ?node_9865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42375 (s : N.State) (i : N.Inputs) :
  R.v42375 (state s) (inputs i) = Zmod.unsigned (N.v42375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42375 s i)) at 1.
  unfold R.v42375, N.v42375.
  unfold R.v6, N.v6.
  rewrite ?node_9858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42376 (s : N.State) (i : N.Inputs) :
  R.v42376 (state s) (inputs i) = Zmod.unsigned (N.v42376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42376 s i)) at 1.
  unfold R.v42376, N.v42376.
  rewrite ?node_42374.
  rewrite ?node_42375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42377 (s : N.State) (i : N.Inputs) :
  R.v42377 (state s) (inputs i) = Zmod.unsigned (N.v42377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42377 s i)) at 1.
  unfold R.v42377, N.v42377.
  unfold R.v16484, N.v16484.
  rewrite ?node_42376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42378 (s : N.State) (i : N.Inputs) :
  R.v42378 (state s) (inputs i) = Zmod.unsigned (N.v42378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42378 s i)) at 1.
  unfold R.v42378, N.v42378.
  rewrite ?node_42371.
  rewrite ?node_42372.
  rewrite ?node_42373.
  rewrite ?node_42377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42379 (s : N.State) (i : N.Inputs) :
  R.v42379 (state s) (inputs i) = Zmod.unsigned (N.v42379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42379 s i)) at 1.
  unfold R.v42379, N.v42379.
  unfold R.v6, N.v6.
  rewrite ?node_42378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42380 (s : N.State) (i : N.Inputs) :
  R.v42380 (state s) (inputs i) = Zmod.unsigned (N.v42380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42380 s i)) at 1.
  unfold R.v42380, N.v42380.
  rewrite ?node_9886.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42381 (s : N.State) (i : N.Inputs) :
  R.v42381 (state s) (inputs i) = Zmod.unsigned (N.v42381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42381 s i)) at 1.
  unfold R.v42381, N.v42381.
  unfold R.v6, N.v6.
  rewrite ?node_10037.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42382 (s : N.State) (i : N.Inputs) :
  R.v42382 (state s) (inputs i) = Zmod.unsigned (N.v42382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42382 s i)) at 1.
  unfold R.v42382, N.v42382.
  unfold R.v6, N.v6.
  rewrite ?node_10090.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42383 (s : N.State) (i : N.Inputs) :
  R.v42383 (state s) (inputs i) = Zmod.unsigned (N.v42383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42383 s i)) at 1.
  unfold R.v42383, N.v42383.
  rewrite ?node_42380.
  rewrite ?node_42381.
  rewrite ?node_42382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42384 (s : N.State) (i : N.Inputs) :
  R.v42384 (state s) (inputs i) = Zmod.unsigned (N.v42384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42384 s i)) at 1.
  unfold R.v42384, N.v42384.
  rewrite ?node_42379.
  rewrite ?node_42383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42385 (s : N.State) (i : N.Inputs) :
  R.v42385 (state s) (inputs i) = Zmod.unsigned (N.v42385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42385 s i)) at 1.
  unfold R.v42385, N.v42385.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42386 (s : N.State) (i : N.Inputs) :
  R.v42386 (state s) (inputs i) = Zmod.unsigned (N.v42386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42386 s i)) at 1.
  unfold R.v42386, N.v42386.
  rewrite ?node_9873.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42387 (s : N.State) (i : N.Inputs) :
  R.v42387 (state s) (inputs i) = Zmod.unsigned (N.v42387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42387 s i)) at 1.
  unfold R.v42387, N.v42387.
  unfold R.v6, N.v6.
  rewrite ?node_9865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42388 (s : N.State) (i : N.Inputs) :
  R.v42388 (state s) (inputs i) = Zmod.unsigned (N.v42388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42388 s i)) at 1.
  unfold R.v42388, N.v42388.
  unfold R.v6, N.v6.
  rewrite ?node_9858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42389 (s : N.State) (i : N.Inputs) :
  R.v42389 (state s) (inputs i) = Zmod.unsigned (N.v42389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42389 s i)) at 1.
  unfold R.v42389, N.v42389.
  rewrite ?node_42387.
  rewrite ?node_42388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42390 (s : N.State) (i : N.Inputs) :
  R.v42390 (state s) (inputs i) = Zmod.unsigned (N.v42390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42390 s i)) at 1.
  unfold R.v42390, N.v42390.
  unfold R.v16484, N.v16484.
  rewrite ?node_42389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42391 (s : N.State) (i : N.Inputs) :
  R.v42391 (state s) (inputs i) = Zmod.unsigned (N.v42391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42391 s i)) at 1.
  unfold R.v42391, N.v42391.
  rewrite ?node_42386.
  rewrite ?node_42390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42392 (s : N.State) (i : N.Inputs) :
  R.v42392 (state s) (inputs i) = Zmod.unsigned (N.v42392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42392 s i)) at 1.
  unfold R.v42392, N.v42392.
  unfold R.v6, N.v6.
  rewrite ?node_42391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42393 (s : N.State) (i : N.Inputs) :
  R.v42393 (state s) (inputs i) = Zmod.unsigned (N.v42393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42393 s i)) at 1.
  unfold R.v42393, N.v42393.
  rewrite ?node_9874.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42394 (s : N.State) (i : N.Inputs) :
  R.v42394 (state s) (inputs i) = Zmod.unsigned (N.v42394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42394 s i)) at 1.
  unfold R.v42394, N.v42394.
  unfold R.v6, N.v6.
  rewrite ?node_10037.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42395 (s : N.State) (i : N.Inputs) :
  R.v42395 (state s) (inputs i) = Zmod.unsigned (N.v42395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42395 s i)) at 1.
  unfold R.v42395, N.v42395.
  rewrite ?node_42393.
  rewrite ?node_42394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42396 (s : N.State) (i : N.Inputs) :
  R.v42396 (state s) (inputs i) = Zmod.unsigned (N.v42396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42396 s i)) at 1.
  unfold R.v42396, N.v42396.
  rewrite ?node_42392.
  rewrite ?node_42395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42397 (s : N.State) (i : N.Inputs) :
  R.v42397 (state s) (inputs i) = Zmod.unsigned (N.v42397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42397 s i)) at 1.
  unfold R.v42397, N.v42397.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42398 (s : N.State) (i : N.Inputs) :
  R.v42398 (state s) (inputs i) = Zmod.unsigned (N.v42398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42398 s i)) at 1.
  unfold R.v42398, N.v42398.
  rewrite ?node_9885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42399 (s : N.State) (i : N.Inputs) :
  R.v42399 (state s) (inputs i) = Zmod.unsigned (N.v42399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42399 s i)) at 1.
  unfold R.v42399, N.v42399.
  unfold R.v6, N.v6.
  rewrite ?node_9881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42400 (s : N.State) (i : N.Inputs) :
  R.v42400 (state s) (inputs i) = Zmod.unsigned (N.v42400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42400 s i)) at 1.
  unfold R.v42400, N.v42400.
  unfold R.v6, N.v6.
  rewrite ?node_9874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42401 (s : N.State) (i : N.Inputs) :
  R.v42401 (state s) (inputs i) = Zmod.unsigned (N.v42401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42401 s i)) at 1.
  unfold R.v42401, N.v42401.
  rewrite ?node_42399.
  rewrite ?node_42400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42402 (s : N.State) (i : N.Inputs) :
  R.v42402 (state s) (inputs i) = Zmod.unsigned (N.v42402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42402 s i)) at 1.
  unfold R.v42402, N.v42402.
  unfold R.v16484, N.v16484.
  rewrite ?node_42401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42403 (s : N.State) (i : N.Inputs) :
  R.v42403 (state s) (inputs i) = Zmod.unsigned (N.v42403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42403 s i)) at 1.
  unfold R.v42403, N.v42403.
  rewrite ?node_42398.
  rewrite ?node_42402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42404 (s : N.State) (i : N.Inputs) :
  R.v42404 (state s) (inputs i) = Zmod.unsigned (N.v42404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42404 s i)) at 1.
  unfold R.v42404, N.v42404.
  unfold R.v6, N.v6.
  rewrite ?node_42403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42405 (s : N.State) (i : N.Inputs) :
  R.v42405 (state s) (inputs i) = Zmod.unsigned (N.v42405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42405 s i)) at 1.
  unfold R.v42405, N.v42405.
  rewrite ?node_9886.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42406 (s : N.State) (i : N.Inputs) :
  R.v42406 (state s) (inputs i) = Zmod.unsigned (N.v42406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42406 s i)) at 1.
  unfold R.v42406, N.v42406.
  unfold R.v6, N.v6.
  rewrite ?node_10090.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42407 (s : N.State) (i : N.Inputs) :
  R.v42407 (state s) (inputs i) = Zmod.unsigned (N.v42407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42407 s i)) at 1.
  unfold R.v42407, N.v42407.
  rewrite ?node_42405.
  rewrite ?node_42406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42408 (s : N.State) (i : N.Inputs) :
  R.v42408 (state s) (inputs i) = Zmod.unsigned (N.v42408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42408 s i)) at 1.
  unfold R.v42408, N.v42408.
  rewrite ?node_42404.
  rewrite ?node_42407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42409 (s : N.State) (i : N.Inputs) :
  R.v42409 (state s) (inputs i) = Zmod.unsigned (N.v42409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42409 s i)) at 1.
  unfold R.v42409, N.v42409.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42410 (s : N.State) (i : N.Inputs) :
  R.v42410 (state s) (inputs i) = Zmod.unsigned (N.v42410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42410 s i)) at 1.
  unfold R.v42410, N.v42410.
  rewrite ?node_9905.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42411 (s : N.State) (i : N.Inputs) :
  R.v42411 (state s) (inputs i) = Zmod.unsigned (N.v42411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42411 s i)) at 1.
  unfold R.v42411, N.v42411.
  rewrite ?node_9901.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42412 (s : N.State) (i : N.Inputs) :
  R.v42412 (state s) (inputs i) = Zmod.unsigned (N.v42412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42412 s i)) at 1.
  unfold R.v42412, N.v42412.
  rewrite ?node_9897.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42413 (s : N.State) (i : N.Inputs) :
  R.v42413 (state s) (inputs i) = Zmod.unsigned (N.v42413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42413 s i)) at 1.
  unfold R.v42413, N.v42413.
  unfold R.v6, N.v6.
  rewrite ?node_9893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42414 (s : N.State) (i : N.Inputs) :
  R.v42414 (state s) (inputs i) = Zmod.unsigned (N.v42414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42414 s i)) at 1.
  unfold R.v42414, N.v42414.
  unfold R.v6, N.v6.
  rewrite ?node_9890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42415 (s : N.State) (i : N.Inputs) :
  R.v42415 (state s) (inputs i) = Zmod.unsigned (N.v42415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42415 s i)) at 1.
  unfold R.v42415, N.v42415.
  rewrite ?node_42413.
  rewrite ?node_42414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42416 (s : N.State) (i : N.Inputs) :
  R.v42416 (state s) (inputs i) = Zmod.unsigned (N.v42416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42416 s i)) at 1.
  unfold R.v42416, N.v42416.
  unfold R.v16484, N.v16484.
  rewrite ?node_42415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42417 (s : N.State) (i : N.Inputs) :
  R.v42417 (state s) (inputs i) = Zmod.unsigned (N.v42417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42417 s i)) at 1.
  unfold R.v42417, N.v42417.
  rewrite ?node_42410.
  rewrite ?node_42411.
  rewrite ?node_42412.
  rewrite ?node_42416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42418 (s : N.State) (i : N.Inputs) :
  R.v42418 (state s) (inputs i) = Zmod.unsigned (N.v42418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42418 s i)) at 1.
  unfold R.v42418, N.v42418.
  unfold R.v6, N.v6.
  rewrite ?node_42417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42419 (s : N.State) (i : N.Inputs) :
  R.v42419 (state s) (inputs i) = Zmod.unsigned (N.v42419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42419 s i)) at 1.
  unfold R.v42419, N.v42419.
  rewrite ?node_9906.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42420 (s : N.State) (i : N.Inputs) :
  R.v42420 (state s) (inputs i) = Zmod.unsigned (N.v42420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42420 s i)) at 1.
  unfold R.v42420, N.v42420.
  unfold R.v6, N.v6.
  rewrite ?node_10054.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42421 (s : N.State) (i : N.Inputs) :
  R.v42421 (state s) (inputs i) = Zmod.unsigned (N.v42421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42421 s i)) at 1.
  unfold R.v42421, N.v42421.
  unfold R.v6, N.v6.
  rewrite ?node_10094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42422 (s : N.State) (i : N.Inputs) :
  R.v42422 (state s) (inputs i) = Zmod.unsigned (N.v42422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42422 s i)) at 1.
  unfold R.v42422, N.v42422.
  rewrite ?node_42419.
  rewrite ?node_42420.
  rewrite ?node_42421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42423 (s : N.State) (i : N.Inputs) :
  R.v42423 (state s) (inputs i) = Zmod.unsigned (N.v42423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42423 s i)) at 1.
  unfold R.v42423, N.v42423.
  rewrite ?node_42418.
  rewrite ?node_42422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42424 (s : N.State) (i : N.Inputs) :
  R.v42424 (state s) (inputs i) = Zmod.unsigned (N.v42424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42424 s i)) at 1.
  unfold R.v42424, N.v42424.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42425 (s : N.State) (i : N.Inputs) :
  R.v42425 (state s) (inputs i) = Zmod.unsigned (N.v42425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42425 s i)) at 1.
  unfold R.v42425, N.v42425.
  rewrite ?node_9897.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42426 (s : N.State) (i : N.Inputs) :
  R.v42426 (state s) (inputs i) = Zmod.unsigned (N.v42426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42426 s i)) at 1.
  unfold R.v42426, N.v42426.
  unfold R.v6, N.v6.
  rewrite ?node_9893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42427 (s : N.State) (i : N.Inputs) :
  R.v42427 (state s) (inputs i) = Zmod.unsigned (N.v42427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42427 s i)) at 1.
  unfold R.v42427, N.v42427.
  unfold R.v6, N.v6.
  rewrite ?node_9890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42428 (s : N.State) (i : N.Inputs) :
  R.v42428 (state s) (inputs i) = Zmod.unsigned (N.v42428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42428 s i)) at 1.
  unfold R.v42428, N.v42428.
  rewrite ?node_42426.
  rewrite ?node_42427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42429 (s : N.State) (i : N.Inputs) :
  R.v42429 (state s) (inputs i) = Zmod.unsigned (N.v42429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42429 s i)) at 1.
  unfold R.v42429, N.v42429.
  unfold R.v16484, N.v16484.
  rewrite ?node_42428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42430 (s : N.State) (i : N.Inputs) :
  R.v42430 (state s) (inputs i) = Zmod.unsigned (N.v42430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42430 s i)) at 1.
  unfold R.v42430, N.v42430.
  rewrite ?node_42425.
  rewrite ?node_42429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42431 (s : N.State) (i : N.Inputs) :
  R.v42431 (state s) (inputs i) = Zmod.unsigned (N.v42431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42431 s i)) at 1.
  unfold R.v42431, N.v42431.
  unfold R.v6, N.v6.
  rewrite ?node_42430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42432 (s : N.State) (i : N.Inputs) :
  R.v42432 (state s) (inputs i) = Zmod.unsigned (N.v42432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42432 s i)) at 1.
  unfold R.v42432, N.v42432.
  rewrite ?node_9898.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42433 (s : N.State) (i : N.Inputs) :
  R.v42433 (state s) (inputs i) = Zmod.unsigned (N.v42433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42433 s i)) at 1.
  unfold R.v42433, N.v42433.
  unfold R.v6, N.v6.
  rewrite ?node_10054.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42434 (s : N.State) (i : N.Inputs) :
  R.v42434 (state s) (inputs i) = Zmod.unsigned (N.v42434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42434 s i)) at 1.
  unfold R.v42434, N.v42434.
  rewrite ?node_42432.
  rewrite ?node_42433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42435 (s : N.State) (i : N.Inputs) :
  R.v42435 (state s) (inputs i) = Zmod.unsigned (N.v42435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42435 s i)) at 1.
  unfold R.v42435, N.v42435.
  rewrite ?node_42431.
  rewrite ?node_42434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42436 (s : N.State) (i : N.Inputs) :
  R.v42436 (state s) (inputs i) = Zmod.unsigned (N.v42436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42436 s i)) at 1.
  unfold R.v42436, N.v42436.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42437 (s : N.State) (i : N.Inputs) :
  R.v42437 (state s) (inputs i) = Zmod.unsigned (N.v42437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42437 s i)) at 1.
  unfold R.v42437, N.v42437.
  rewrite ?node_9905.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42438 (s : N.State) (i : N.Inputs) :
  R.v42438 (state s) (inputs i) = Zmod.unsigned (N.v42438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42438 s i)) at 1.
  unfold R.v42438, N.v42438.
  unfold R.v6, N.v6.
  rewrite ?node_9901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42439 (s : N.State) (i : N.Inputs) :
  R.v42439 (state s) (inputs i) = Zmod.unsigned (N.v42439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42439 s i)) at 1.
  unfold R.v42439, N.v42439.
  unfold R.v6, N.v6.
  rewrite ?node_9898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42440 (s : N.State) (i : N.Inputs) :
  R.v42440 (state s) (inputs i) = Zmod.unsigned (N.v42440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42440 s i)) at 1.
  unfold R.v42440, N.v42440.
  rewrite ?node_42438.
  rewrite ?node_42439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42441 (s : N.State) (i : N.Inputs) :
  R.v42441 (state s) (inputs i) = Zmod.unsigned (N.v42441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42441 s i)) at 1.
  unfold R.v42441, N.v42441.
  unfold R.v16484, N.v16484.
  rewrite ?node_42440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42442 (s : N.State) (i : N.Inputs) :
  R.v42442 (state s) (inputs i) = Zmod.unsigned (N.v42442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42442 s i)) at 1.
  unfold R.v42442, N.v42442.
  rewrite ?node_42437.
  rewrite ?node_42441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42443 (s : N.State) (i : N.Inputs) :
  R.v42443 (state s) (inputs i) = Zmod.unsigned (N.v42443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42443 s i)) at 1.
  unfold R.v42443, N.v42443.
  unfold R.v6, N.v6.
  rewrite ?node_42442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42444 (s : N.State) (i : N.Inputs) :
  R.v42444 (state s) (inputs i) = Zmod.unsigned (N.v42444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42444 s i)) at 1.
  unfold R.v42444, N.v42444.
  rewrite ?node_9906.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42445 (s : N.State) (i : N.Inputs) :
  R.v42445 (state s) (inputs i) = Zmod.unsigned (N.v42445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42445 s i)) at 1.
  unfold R.v42445, N.v42445.
  unfold R.v6, N.v6.
  rewrite ?node_10094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42446 (s : N.State) (i : N.Inputs) :
  R.v42446 (state s) (inputs i) = Zmod.unsigned (N.v42446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42446 s i)) at 1.
  unfold R.v42446, N.v42446.
  rewrite ?node_42444.
  rewrite ?node_42445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42447 (s : N.State) (i : N.Inputs) :
  R.v42447 (state s) (inputs i) = Zmod.unsigned (N.v42447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42447 s i)) at 1.
  unfold R.v42447, N.v42447.
  rewrite ?node_42443.
  rewrite ?node_42446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42448 (s : N.State) (i : N.Inputs) :
  R.v42448 (state s) (inputs i) = Zmod.unsigned (N.v42448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42448 s i)) at 1.
  unfold R.v42448, N.v42448.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42449 (s : N.State) (i : N.Inputs) :
  R.v42449 (state s) (inputs i) = Zmod.unsigned (N.v42449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42449 s i)) at 1.
  unfold R.v42449, N.v42449.
  rewrite ?node_9923.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42450 (s : N.State) (i : N.Inputs) :
  R.v42450 (state s) (inputs i) = Zmod.unsigned (N.v42450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42450 s i)) at 1.
  unfold R.v42450, N.v42450.
  rewrite ?node_9919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42451 (s : N.State) (i : N.Inputs) :
  R.v42451 (state s) (inputs i) = Zmod.unsigned (N.v42451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42451 s i)) at 1.
  unfold R.v42451, N.v42451.
  rewrite ?node_9917.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42452 (s : N.State) (i : N.Inputs) :
  R.v42452 (state s) (inputs i) = Zmod.unsigned (N.v42452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42452 s i)) at 1.
  unfold R.v42452, N.v42452.
  unfold R.v6, N.v6.
  rewrite ?node_9913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42453 (s : N.State) (i : N.Inputs) :
  R.v42453 (state s) (inputs i) = Zmod.unsigned (N.v42453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42453 s i)) at 1.
  unfold R.v42453, N.v42453.
  unfold R.v6, N.v6.
  rewrite ?node_9910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42454 (s : N.State) (i : N.Inputs) :
  R.v42454 (state s) (inputs i) = Zmod.unsigned (N.v42454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42454 s i)) at 1.
  unfold R.v42454, N.v42454.
  rewrite ?node_42452.
  rewrite ?node_42453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42455 (s : N.State) (i : N.Inputs) :
  R.v42455 (state s) (inputs i) = Zmod.unsigned (N.v42455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42455 s i)) at 1.
  unfold R.v42455, N.v42455.
  unfold R.v16484, N.v16484.
  rewrite ?node_42454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42456 (s : N.State) (i : N.Inputs) :
  R.v42456 (state s) (inputs i) = Zmod.unsigned (N.v42456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42456 s i)) at 1.
  unfold R.v42456, N.v42456.
  rewrite ?node_42449.
  rewrite ?node_42450.
  rewrite ?node_42451.
  rewrite ?node_42455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42457 (s : N.State) (i : N.Inputs) :
  R.v42457 (state s) (inputs i) = Zmod.unsigned (N.v42457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42457 s i)) at 1.
  unfold R.v42457, N.v42457.
  unfold R.v6, N.v6.
  rewrite ?node_42456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42458 (s : N.State) (i : N.Inputs) :
  R.v42458 (state s) (inputs i) = Zmod.unsigned (N.v42458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42458 s i)) at 1.
  unfold R.v42458, N.v42458.
  rewrite ?node_9924.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42459 (s : N.State) (i : N.Inputs) :
  R.v42459 (state s) (inputs i) = Zmod.unsigned (N.v42459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42459 s i)) at 1.
  unfold R.v42459, N.v42459.
  unfold R.v6, N.v6.
  rewrite ?node_10074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42460 (s : N.State) (i : N.Inputs) :
  R.v42460 (state s) (inputs i) = Zmod.unsigned (N.v42460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42460 s i)) at 1.
  unfold R.v42460, N.v42460.
  unfold R.v6, N.v6.
  rewrite ?node_10103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42461 (s : N.State) (i : N.Inputs) :
  R.v42461 (state s) (inputs i) = Zmod.unsigned (N.v42461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42461 s i)) at 1.
  unfold R.v42461, N.v42461.
  rewrite ?node_42458.
  rewrite ?node_42459.
  rewrite ?node_42460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42462 (s : N.State) (i : N.Inputs) :
  R.v42462 (state s) (inputs i) = Zmod.unsigned (N.v42462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42462 s i)) at 1.
  unfold R.v42462, N.v42462.
  rewrite ?node_42457.
  rewrite ?node_42461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42463 (s : N.State) (i : N.Inputs) :
  R.v42463 (state s) (inputs i) = Zmod.unsigned (N.v42463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42463 s i)) at 1.
  unfold R.v42463, N.v42463.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42464 (s : N.State) (i : N.Inputs) :
  R.v42464 (state s) (inputs i) = Zmod.unsigned (N.v42464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42464 s i)) at 1.
  unfold R.v42464, N.v42464.
  rewrite ?node_9917.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42465 (s : N.State) (i : N.Inputs) :
  R.v42465 (state s) (inputs i) = Zmod.unsigned (N.v42465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42465 s i)) at 1.
  unfold R.v42465, N.v42465.
  unfold R.v6, N.v6.
  rewrite ?node_9913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42466 (s : N.State) (i : N.Inputs) :
  R.v42466 (state s) (inputs i) = Zmod.unsigned (N.v42466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42466 s i)) at 1.
  unfold R.v42466, N.v42466.
  unfold R.v6, N.v6.
  rewrite ?node_9910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42467 (s : N.State) (i : N.Inputs) :
  R.v42467 (state s) (inputs i) = Zmod.unsigned (N.v42467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42467 s i)) at 1.
  unfold R.v42467, N.v42467.
  rewrite ?node_42465.
  rewrite ?node_42466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42468 (s : N.State) (i : N.Inputs) :
  R.v42468 (state s) (inputs i) = Zmod.unsigned (N.v42468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42468 s i)) at 1.
  unfold R.v42468, N.v42468.
  unfold R.v16484, N.v16484.
  rewrite ?node_42467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42469 (s : N.State) (i : N.Inputs) :
  R.v42469 (state s) (inputs i) = Zmod.unsigned (N.v42469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42469 s i)) at 1.
  unfold R.v42469, N.v42469.
  rewrite ?node_42464.
  rewrite ?node_42468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42470 (s : N.State) (i : N.Inputs) :
  R.v42470 (state s) (inputs i) = Zmod.unsigned (N.v42470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42470 s i)) at 1.
  unfold R.v42470, N.v42470.
  unfold R.v6, N.v6.
  rewrite ?node_42469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42471 (s : N.State) (i : N.Inputs) :
  R.v42471 (state s) (inputs i) = Zmod.unsigned (N.v42471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42471 s i)) at 1.
  unfold R.v42471, N.v42471.
  rewrite ?node_9918.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42472 (s : N.State) (i : N.Inputs) :
  R.v42472 (state s) (inputs i) = Zmod.unsigned (N.v42472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42472 s i)) at 1.
  unfold R.v42472, N.v42472.
  unfold R.v6, N.v6.
  rewrite ?node_10074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42473 (s : N.State) (i : N.Inputs) :
  R.v42473 (state s) (inputs i) = Zmod.unsigned (N.v42473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42473 s i)) at 1.
  unfold R.v42473, N.v42473.
  rewrite ?node_42471.
  rewrite ?node_42472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42474 (s : N.State) (i : N.Inputs) :
  R.v42474 (state s) (inputs i) = Zmod.unsigned (N.v42474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42474 s i)) at 1.
  unfold R.v42474, N.v42474.
  rewrite ?node_42470.
  rewrite ?node_42473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42475 (s : N.State) (i : N.Inputs) :
  R.v42475 (state s) (inputs i) = Zmod.unsigned (N.v42475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42475 s i)) at 1.
  unfold R.v42475, N.v42475.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42476 (s : N.State) (i : N.Inputs) :
  R.v42476 (state s) (inputs i) = Zmod.unsigned (N.v42476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42476 s i)) at 1.
  unfold R.v42476, N.v42476.
  rewrite ?node_9923.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42477 (s : N.State) (i : N.Inputs) :
  R.v42477 (state s) (inputs i) = Zmod.unsigned (N.v42477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42477 s i)) at 1.
  unfold R.v42477, N.v42477.
  unfold R.v6, N.v6.
  rewrite ?node_9919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42478 (s : N.State) (i : N.Inputs) :
  R.v42478 (state s) (inputs i) = Zmod.unsigned (N.v42478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42478 s i)) at 1.
  unfold R.v42478, N.v42478.
  unfold R.v6, N.v6.
  rewrite ?node_9918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42479 (s : N.State) (i : N.Inputs) :
  R.v42479 (state s) (inputs i) = Zmod.unsigned (N.v42479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42479 s i)) at 1.
  unfold R.v42479, N.v42479.
  rewrite ?node_42477.
  rewrite ?node_42478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42480 (s : N.State) (i : N.Inputs) :
  R.v42480 (state s) (inputs i) = Zmod.unsigned (N.v42480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42480 s i)) at 1.
  unfold R.v42480, N.v42480.
  unfold R.v16484, N.v16484.
  rewrite ?node_42479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42481 (s : N.State) (i : N.Inputs) :
  R.v42481 (state s) (inputs i) = Zmod.unsigned (N.v42481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42481 s i)) at 1.
  unfold R.v42481, N.v42481.
  rewrite ?node_42476.
  rewrite ?node_42480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42482 (s : N.State) (i : N.Inputs) :
  R.v42482 (state s) (inputs i) = Zmod.unsigned (N.v42482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42482 s i)) at 1.
  unfold R.v42482, N.v42482.
  unfold R.v6, N.v6.
  rewrite ?node_42481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42483 (s : N.State) (i : N.Inputs) :
  R.v42483 (state s) (inputs i) = Zmod.unsigned (N.v42483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42483 s i)) at 1.
  unfold R.v42483, N.v42483.
  rewrite ?node_9924.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42484 (s : N.State) (i : N.Inputs) :
  R.v42484 (state s) (inputs i) = Zmod.unsigned (N.v42484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42484 s i)) at 1.
  unfold R.v42484, N.v42484.
  unfold R.v6, N.v6.
  rewrite ?node_10103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42485 (s : N.State) (i : N.Inputs) :
  R.v42485 (state s) (inputs i) = Zmod.unsigned (N.v42485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42485 s i)) at 1.
  unfold R.v42485, N.v42485.
  rewrite ?node_42483.
  rewrite ?node_42484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42486 (s : N.State) (i : N.Inputs) :
  R.v42486 (state s) (inputs i) = Zmod.unsigned (N.v42486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42486 s i)) at 1.
  unfold R.v42486, N.v42486.
  rewrite ?node_42482.
  rewrite ?node_42485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42487 (s : N.State) (i : N.Inputs) :
  R.v42487 (state s) (inputs i) = Zmod.unsigned (N.v42487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42487 s i)) at 1.
  unfold R.v42487, N.v42487.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42488 (s : N.State) (i : N.Inputs) :
  R.v42488 (state s) (inputs i) = Zmod.unsigned (N.v42488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42488 s i)) at 1.
  unfold R.v42488, N.v42488.
  rewrite ?node_10002.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42489 (s : N.State) (i : N.Inputs) :
  R.v42489 (state s) (inputs i) = Zmod.unsigned (N.v42489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42489 s i)) at 1.
  unfold R.v42489, N.v42489.
  rewrite ?node_9998.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42490 (s : N.State) (i : N.Inputs) :
  R.v42490 (state s) (inputs i) = Zmod.unsigned (N.v42490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42490 s i)) at 1.
  unfold R.v42490, N.v42490.
  rewrite ?node_9990.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42491 (s : N.State) (i : N.Inputs) :
  R.v42491 (state s) (inputs i) = Zmod.unsigned (N.v42491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42491 s i)) at 1.
  unfold R.v42491, N.v42491.
  unfold R.v6, N.v6.
  rewrite ?node_9982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42492 (s : N.State) (i : N.Inputs) :
  R.v42492 (state s) (inputs i) = Zmod.unsigned (N.v42492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42492 s i)) at 1.
  unfold R.v42492, N.v42492.
  unfold R.v6, N.v6.
  rewrite ?node_9975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42493 (s : N.State) (i : N.Inputs) :
  R.v42493 (state s) (inputs i) = Zmod.unsigned (N.v42493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42493 s i)) at 1.
  unfold R.v42493, N.v42493.
  rewrite ?node_42491.
  rewrite ?node_42492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42494 (s : N.State) (i : N.Inputs) :
  R.v42494 (state s) (inputs i) = Zmod.unsigned (N.v42494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42494 s i)) at 1.
  unfold R.v42494, N.v42494.
  unfold R.v16484, N.v16484.
  rewrite ?node_42493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42495 (s : N.State) (i : N.Inputs) :
  R.v42495 (state s) (inputs i) = Zmod.unsigned (N.v42495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42495 s i)) at 1.
  unfold R.v42495, N.v42495.
  rewrite ?node_42488.
  rewrite ?node_42489.
  rewrite ?node_42490.
  rewrite ?node_42494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42496 (s : N.State) (i : N.Inputs) :
  R.v42496 (state s) (inputs i) = Zmod.unsigned (N.v42496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42496 s i)) at 1.
  unfold R.v42496, N.v42496.
  unfold R.v6, N.v6.
  rewrite ?node_42495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42497 (s : N.State) (i : N.Inputs) :
  R.v42497 (state s) (inputs i) = Zmod.unsigned (N.v42497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42497 s i)) at 1.
  unfold R.v42497, N.v42497.
  rewrite ?node_10003.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42498 (s : N.State) (i : N.Inputs) :
  R.v42498 (state s) (inputs i) = Zmod.unsigned (N.v42498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42498 s i)) at 1.
  unfold R.v42498, N.v42498.
  unfold R.v6, N.v6.
  rewrite ?node_10157.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42499 (s : N.State) (i : N.Inputs) :
  R.v42499 (state s) (inputs i) = Zmod.unsigned (N.v42499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42499 s i)) at 1.
  unfold R.v42499, N.v42499.
  unfold R.v6, N.v6.
  rewrite ?node_10241.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42500 (s : N.State) (i : N.Inputs) :
  R.v42500 (state s) (inputs i) = Zmod.unsigned (N.v42500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42500 s i)) at 1.
  unfold R.v42500, N.v42500.
  rewrite ?node_42497.
  rewrite ?node_42498.
  rewrite ?node_42499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42501 (s : N.State) (i : N.Inputs) :
  R.v42501 (state s) (inputs i) = Zmod.unsigned (N.v42501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42501 s i)) at 1.
  unfold R.v42501, N.v42501.
  rewrite ?node_42496.
  rewrite ?node_42500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42502 (s : N.State) (i : N.Inputs) :
  R.v42502 (state s) (inputs i) = Zmod.unsigned (N.v42502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42502 s i)) at 1.
  unfold R.v42502, N.v42502.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42503 (s : N.State) (i : N.Inputs) :
  R.v42503 (state s) (inputs i) = Zmod.unsigned (N.v42503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42503 s i)) at 1.
  unfold R.v42503, N.v42503.
  rewrite ?node_9990.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42504 (s : N.State) (i : N.Inputs) :
  R.v42504 (state s) (inputs i) = Zmod.unsigned (N.v42504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42504 s i)) at 1.
  unfold R.v42504, N.v42504.
  unfold R.v6, N.v6.
  rewrite ?node_9982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42505 (s : N.State) (i : N.Inputs) :
  R.v42505 (state s) (inputs i) = Zmod.unsigned (N.v42505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42505 s i)) at 1.
  unfold R.v42505, N.v42505.
  unfold R.v6, N.v6.
  rewrite ?node_9975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42506 (s : N.State) (i : N.Inputs) :
  R.v42506 (state s) (inputs i) = Zmod.unsigned (N.v42506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42506 s i)) at 1.
  unfold R.v42506, N.v42506.
  rewrite ?node_42504.
  rewrite ?node_42505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42507 (s : N.State) (i : N.Inputs) :
  R.v42507 (state s) (inputs i) = Zmod.unsigned (N.v42507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42507 s i)) at 1.
  unfold R.v42507, N.v42507.
  unfold R.v16484, N.v16484.
  rewrite ?node_42506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42508 (s : N.State) (i : N.Inputs) :
  R.v42508 (state s) (inputs i) = Zmod.unsigned (N.v42508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42508 s i)) at 1.
  unfold R.v42508, N.v42508.
  rewrite ?node_42503.
  rewrite ?node_42507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42509 (s : N.State) (i : N.Inputs) :
  R.v42509 (state s) (inputs i) = Zmod.unsigned (N.v42509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42509 s i)) at 1.
  unfold R.v42509, N.v42509.
  unfold R.v6, N.v6.
  rewrite ?node_42508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42510 (s : N.State) (i : N.Inputs) :
  R.v42510 (state s) (inputs i) = Zmod.unsigned (N.v42510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42510 s i)) at 1.
  unfold R.v42510, N.v42510.
  rewrite ?node_9991.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42511 (s : N.State) (i : N.Inputs) :
  R.v42511 (state s) (inputs i) = Zmod.unsigned (N.v42511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42511 s i)) at 1.
  unfold R.v42511, N.v42511.
  unfold R.v6, N.v6.
  rewrite ?node_10157.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42512 (s : N.State) (i : N.Inputs) :
  R.v42512 (state s) (inputs i) = Zmod.unsigned (N.v42512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42512 s i)) at 1.
  unfold R.v42512, N.v42512.
  rewrite ?node_42510.
  rewrite ?node_42511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42513 (s : N.State) (i : N.Inputs) :
  R.v42513 (state s) (inputs i) = Zmod.unsigned (N.v42513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42513 s i)) at 1.
  unfold R.v42513, N.v42513.
  rewrite ?node_42509.
  rewrite ?node_42512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42514 (s : N.State) (i : N.Inputs) :
  R.v42514 (state s) (inputs i) = Zmod.unsigned (N.v42514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42514 s i)) at 1.
  unfold R.v42514, N.v42514.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42515 (s : N.State) (i : N.Inputs) :
  R.v42515 (state s) (inputs i) = Zmod.unsigned (N.v42515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42515 s i)) at 1.
  unfold R.v42515, N.v42515.
  rewrite ?node_10002.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42516 (s : N.State) (i : N.Inputs) :
  R.v42516 (state s) (inputs i) = Zmod.unsigned (N.v42516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42516 s i)) at 1.
  unfold R.v42516, N.v42516.
  unfold R.v6, N.v6.
  rewrite ?node_9998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42517 (s : N.State) (i : N.Inputs) :
  R.v42517 (state s) (inputs i) = Zmod.unsigned (N.v42517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42517 s i)) at 1.
  unfold R.v42517, N.v42517.
  unfold R.v6, N.v6.
  rewrite ?node_9991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42518 (s : N.State) (i : N.Inputs) :
  R.v42518 (state s) (inputs i) = Zmod.unsigned (N.v42518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42518 s i)) at 1.
  unfold R.v42518, N.v42518.
  rewrite ?node_42516.
  rewrite ?node_42517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42519 (s : N.State) (i : N.Inputs) :
  R.v42519 (state s) (inputs i) = Zmod.unsigned (N.v42519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42519 s i)) at 1.
  unfold R.v42519, N.v42519.
  unfold R.v16484, N.v16484.
  rewrite ?node_42518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42520 (s : N.State) (i : N.Inputs) :
  R.v42520 (state s) (inputs i) = Zmod.unsigned (N.v42520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42520 s i)) at 1.
  unfold R.v42520, N.v42520.
  rewrite ?node_42515.
  rewrite ?node_42519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42521 (s : N.State) (i : N.Inputs) :
  R.v42521 (state s) (inputs i) = Zmod.unsigned (N.v42521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42521 s i)) at 1.
  unfold R.v42521, N.v42521.
  unfold R.v6, N.v6.
  rewrite ?node_42520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42522 (s : N.State) (i : N.Inputs) :
  R.v42522 (state s) (inputs i) = Zmod.unsigned (N.v42522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42522 s i)) at 1.
  unfold R.v42522, N.v42522.
  rewrite ?node_10003.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42523 (s : N.State) (i : N.Inputs) :
  R.v42523 (state s) (inputs i) = Zmod.unsigned (N.v42523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42523 s i)) at 1.
  unfold R.v42523, N.v42523.
  unfold R.v6, N.v6.
  rewrite ?node_10241.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42524 (s : N.State) (i : N.Inputs) :
  R.v42524 (state s) (inputs i) = Zmod.unsigned (N.v42524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42524 s i)) at 1.
  unfold R.v42524, N.v42524.
  rewrite ?node_42522.
  rewrite ?node_42523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42525 (s : N.State) (i : N.Inputs) :
  R.v42525 (state s) (inputs i) = Zmod.unsigned (N.v42525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42525 s i)) at 1.
  unfold R.v42525, N.v42525.
  rewrite ?node_42521.
  rewrite ?node_42524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42526 (s : N.State) (i : N.Inputs) :
  R.v42526 (state s) (inputs i) = Zmod.unsigned (N.v42526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42526 s i)) at 1.
  unfold R.v42526, N.v42526.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42527 (s : N.State) (i : N.Inputs) :
  R.v42527 (state s) (inputs i) = Zmod.unsigned (N.v42527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42527 s i)) at 1.
  unfold R.v42527, N.v42527.
  rewrite ?node_10037.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42528 (s : N.State) (i : N.Inputs) :
  R.v42528 (state s) (inputs i) = Zmod.unsigned (N.v42528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42528 s i)) at 1.
  unfold R.v42528, N.v42528.
  rewrite ?node_10033.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42529 (s : N.State) (i : N.Inputs) :
  R.v42529 (state s) (inputs i) = Zmod.unsigned (N.v42529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42529 s i)) at 1.
  unfold R.v42529, N.v42529.
  rewrite ?node_10025.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42530 (s : N.State) (i : N.Inputs) :
  R.v42530 (state s) (inputs i) = Zmod.unsigned (N.v42530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42530 s i)) at 1.
  unfold R.v42530, N.v42530.
  unfold R.v6, N.v6.
  rewrite ?node_10017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42531 (s : N.State) (i : N.Inputs) :
  R.v42531 (state s) (inputs i) = Zmod.unsigned (N.v42531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42531 s i)) at 1.
  unfold R.v42531, N.v42531.
  unfold R.v6, N.v6.
  rewrite ?node_10010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42532 (s : N.State) (i : N.Inputs) :
  R.v42532 (state s) (inputs i) = Zmod.unsigned (N.v42532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42532 s i)) at 1.
  unfold R.v42532, N.v42532.
  rewrite ?node_42530.
  rewrite ?node_42531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42533 (s : N.State) (i : N.Inputs) :
  R.v42533 (state s) (inputs i) = Zmod.unsigned (N.v42533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42533 s i)) at 1.
  unfold R.v42533, N.v42533.
  unfold R.v16484, N.v16484.
  rewrite ?node_42532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42534 (s : N.State) (i : N.Inputs) :
  R.v42534 (state s) (inputs i) = Zmod.unsigned (N.v42534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42534 s i)) at 1.
  unfold R.v42534, N.v42534.
  rewrite ?node_42527.
  rewrite ?node_42528.
  rewrite ?node_42529.
  rewrite ?node_42533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42535 (s : N.State) (i : N.Inputs) :
  R.v42535 (state s) (inputs i) = Zmod.unsigned (N.v42535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42535 s i)) at 1.
  unfold R.v42535, N.v42535.
  unfold R.v6, N.v6.
  rewrite ?node_42534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42536 (s : N.State) (i : N.Inputs) :
  R.v42536 (state s) (inputs i) = Zmod.unsigned (N.v42536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42536 s i)) at 1.
  unfold R.v42536, N.v42536.
  rewrite ?node_10038.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42537 (s : N.State) (i : N.Inputs) :
  R.v42537 (state s) (inputs i) = Zmod.unsigned (N.v42537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42537 s i)) at 1.
  unfold R.v42537, N.v42537.
  unfold R.v6, N.v6.
  rewrite ?node_10192.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42538 (s : N.State) (i : N.Inputs) :
  R.v42538 (state s) (inputs i) = Zmod.unsigned (N.v42538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42538 s i)) at 1.
  unfold R.v42538, N.v42538.
  unfold R.v6, N.v6.
  rewrite ?node_10245.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42539 (s : N.State) (i : N.Inputs) :
  R.v42539 (state s) (inputs i) = Zmod.unsigned (N.v42539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42539 s i)) at 1.
  unfold R.v42539, N.v42539.
  rewrite ?node_42536.
  rewrite ?node_42537.
  rewrite ?node_42538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42540 (s : N.State) (i : N.Inputs) :
  R.v42540 (state s) (inputs i) = Zmod.unsigned (N.v42540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42540 s i)) at 1.
  unfold R.v42540, N.v42540.
  rewrite ?node_42535.
  rewrite ?node_42539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42541 (s : N.State) (i : N.Inputs) :
  R.v42541 (state s) (inputs i) = Zmod.unsigned (N.v42541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42541 s i)) at 1.
  unfold R.v42541, N.v42541.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42542 (s : N.State) (i : N.Inputs) :
  R.v42542 (state s) (inputs i) = Zmod.unsigned (N.v42542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42542 s i)) at 1.
  unfold R.v42542, N.v42542.
  rewrite ?node_10025.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42543 (s : N.State) (i : N.Inputs) :
  R.v42543 (state s) (inputs i) = Zmod.unsigned (N.v42543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42543 s i)) at 1.
  unfold R.v42543, N.v42543.
  unfold R.v6, N.v6.
  rewrite ?node_10017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42544 (s : N.State) (i : N.Inputs) :
  R.v42544 (state s) (inputs i) = Zmod.unsigned (N.v42544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42544 s i)) at 1.
  unfold R.v42544, N.v42544.
  unfold R.v6, N.v6.
  rewrite ?node_10010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42545 (s : N.State) (i : N.Inputs) :
  R.v42545 (state s) (inputs i) = Zmod.unsigned (N.v42545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42545 s i)) at 1.
  unfold R.v42545, N.v42545.
  rewrite ?node_42543.
  rewrite ?node_42544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42546 (s : N.State) (i : N.Inputs) :
  R.v42546 (state s) (inputs i) = Zmod.unsigned (N.v42546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42546 s i)) at 1.
  unfold R.v42546, N.v42546.
  unfold R.v16484, N.v16484.
  rewrite ?node_42545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42547 (s : N.State) (i : N.Inputs) :
  R.v42547 (state s) (inputs i) = Zmod.unsigned (N.v42547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42547 s i)) at 1.
  unfold R.v42547, N.v42547.
  rewrite ?node_42542.
  rewrite ?node_42546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42548 (s : N.State) (i : N.Inputs) :
  R.v42548 (state s) (inputs i) = Zmod.unsigned (N.v42548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42548 s i)) at 1.
  unfold R.v42548, N.v42548.
  unfold R.v6, N.v6.
  rewrite ?node_42547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42549 (s : N.State) (i : N.Inputs) :
  R.v42549 (state s) (inputs i) = Zmod.unsigned (N.v42549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42549 s i)) at 1.
  unfold R.v42549, N.v42549.
  rewrite ?node_10026.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42550 (s : N.State) (i : N.Inputs) :
  R.v42550 (state s) (inputs i) = Zmod.unsigned (N.v42550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42550 s i)) at 1.
  unfold R.v42550, N.v42550.
  unfold R.v6, N.v6.
  rewrite ?node_10192.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42551 (s : N.State) (i : N.Inputs) :
  R.v42551 (state s) (inputs i) = Zmod.unsigned (N.v42551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42551 s i)) at 1.
  unfold R.v42551, N.v42551.
  rewrite ?node_42549.
  rewrite ?node_42550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42552 (s : N.State) (i : N.Inputs) :
  R.v42552 (state s) (inputs i) = Zmod.unsigned (N.v42552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42552 s i)) at 1.
  unfold R.v42552, N.v42552.
  rewrite ?node_42548.
  rewrite ?node_42551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42553 (s : N.State) (i : N.Inputs) :
  R.v42553 (state s) (inputs i) = Zmod.unsigned (N.v42553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42553 s i)) at 1.
  unfold R.v42553, N.v42553.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42554 (s : N.State) (i : N.Inputs) :
  R.v42554 (state s) (inputs i) = Zmod.unsigned (N.v42554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42554 s i)) at 1.
  unfold R.v42554, N.v42554.
  rewrite ?node_10037.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42555 (s : N.State) (i : N.Inputs) :
  R.v42555 (state s) (inputs i) = Zmod.unsigned (N.v42555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42555 s i)) at 1.
  unfold R.v42555, N.v42555.
  unfold R.v6, N.v6.
  rewrite ?node_10033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42556 (s : N.State) (i : N.Inputs) :
  R.v42556 (state s) (inputs i) = Zmod.unsigned (N.v42556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42556 s i)) at 1.
  unfold R.v42556, N.v42556.
  unfold R.v6, N.v6.
  rewrite ?node_10026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42557 (s : N.State) (i : N.Inputs) :
  R.v42557 (state s) (inputs i) = Zmod.unsigned (N.v42557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42557 s i)) at 1.
  unfold R.v42557, N.v42557.
  rewrite ?node_42555.
  rewrite ?node_42556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42558 (s : N.State) (i : N.Inputs) :
  R.v42558 (state s) (inputs i) = Zmod.unsigned (N.v42558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42558 s i)) at 1.
  unfold R.v42558, N.v42558.
  unfold R.v16484, N.v16484.
  rewrite ?node_42557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42559 (s : N.State) (i : N.Inputs) :
  R.v42559 (state s) (inputs i) = Zmod.unsigned (N.v42559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42559 s i)) at 1.
  unfold R.v42559, N.v42559.
  rewrite ?node_42554.
  rewrite ?node_42558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42560 (s : N.State) (i : N.Inputs) :
  R.v42560 (state s) (inputs i) = Zmod.unsigned (N.v42560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42560 s i)) at 1.
  unfold R.v42560, N.v42560.
  unfold R.v6, N.v6.
  rewrite ?node_42559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42561 (s : N.State) (i : N.Inputs) :
  R.v42561 (state s) (inputs i) = Zmod.unsigned (N.v42561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42561 s i)) at 1.
  unfold R.v42561, N.v42561.
  rewrite ?node_10038.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42562 (s : N.State) (i : N.Inputs) :
  R.v42562 (state s) (inputs i) = Zmod.unsigned (N.v42562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42562 s i)) at 1.
  unfold R.v42562, N.v42562.
  unfold R.v6, N.v6.
  rewrite ?node_10245.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42563 (s : N.State) (i : N.Inputs) :
  R.v42563 (state s) (inputs i) = Zmod.unsigned (N.v42563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42563 s i)) at 1.
  unfold R.v42563, N.v42563.
  rewrite ?node_42561.
  rewrite ?node_42562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42564 (s : N.State) (i : N.Inputs) :
  R.v42564 (state s) (inputs i) = Zmod.unsigned (N.v42564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42564 s i)) at 1.
  unfold R.v42564, N.v42564.
  rewrite ?node_42560.
  rewrite ?node_42563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42565 (s : N.State) (i : N.Inputs) :
  R.v42565 (state s) (inputs i) = Zmod.unsigned (N.v42565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42565 s i)) at 1.
  unfold R.v42565, N.v42565.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42566 (s : N.State) (i : N.Inputs) :
  R.v42566 (state s) (inputs i) = Zmod.unsigned (N.v42566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42566 s i)) at 1.
  unfold R.v42566, N.v42566.
  rewrite ?node_10054.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42567 (s : N.State) (i : N.Inputs) :
  R.v42567 (state s) (inputs i) = Zmod.unsigned (N.v42567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42567 s i)) at 1.
  unfold R.v42567, N.v42567.
  rewrite ?node_10050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42568 (s : N.State) (i : N.Inputs) :
  R.v42568 (state s) (inputs i) = Zmod.unsigned (N.v42568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42568 s i)) at 1.
  unfold R.v42568, N.v42568.
  rewrite ?node_10046.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42569 (s : N.State) (i : N.Inputs) :
  R.v42569 (state s) (inputs i) = Zmod.unsigned (N.v42569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42569 s i)) at 1.
  unfold R.v42569, N.v42569.
  unfold R.v6, N.v6.
  rewrite ?node_10042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42570 (s : N.State) (i : N.Inputs) :
  R.v42570 (state s) (inputs i) = Zmod.unsigned (N.v42570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42570 s i)) at 1.
  unfold R.v42570, N.v42570.
  unfold R.v6, N.v6.
  rewrite !state_r1086_nr_5F1086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1086_nr_5F1086 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42571 (s : N.State) (i : N.Inputs) :
  R.v42571 (state s) (inputs i) = Zmod.unsigned (N.v42571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42571 s i)) at 1.
  unfold R.v42571, N.v42571.
  rewrite ?node_42569.
  rewrite ?node_42570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42572 (s : N.State) (i : N.Inputs) :
  R.v42572 (state s) (inputs i) = Zmod.unsigned (N.v42572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42572 s i)) at 1.
  unfold R.v42572, N.v42572.
  unfold R.v16484, N.v16484.
  rewrite ?node_42571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42573 (s : N.State) (i : N.Inputs) :
  R.v42573 (state s) (inputs i) = Zmod.unsigned (N.v42573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42573 s i)) at 1.
  unfold R.v42573, N.v42573.
  rewrite ?node_42566.
  rewrite ?node_42567.
  rewrite ?node_42568.
  rewrite ?node_42572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42574 (s : N.State) (i : N.Inputs) :
  R.v42574 (state s) (inputs i) = Zmod.unsigned (N.v42574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42574 s i)) at 1.
  unfold R.v42574, N.v42574.
  unfold R.v6, N.v6.
  rewrite ?node_42573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42575 (s : N.State) (i : N.Inputs) :
  R.v42575 (state s) (inputs i) = Zmod.unsigned (N.v42575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42575 s i)) at 1.
  unfold R.v42575, N.v42575.
  rewrite ?node_10055.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42576 (s : N.State) (i : N.Inputs) :
  R.v42576 (state s) (inputs i) = Zmod.unsigned (N.v42576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42576 s i)) at 1.
  unfold R.v42576, N.v42576.
  unfold R.v6, N.v6.
  rewrite ?node_10209.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42577 (s : N.State) (i : N.Inputs) :
  R.v42577 (state s) (inputs i) = Zmod.unsigned (N.v42577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42577 s i)) at 1.
  unfold R.v42577, N.v42577.
  unfold R.v6, N.v6.
  rewrite ?node_10249.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42578 (s : N.State) (i : N.Inputs) :
  R.v42578 (state s) (inputs i) = Zmod.unsigned (N.v42578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42578 s i)) at 1.
  unfold R.v42578, N.v42578.
  rewrite ?node_42575.
  rewrite ?node_42576.
  rewrite ?node_42577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42579 (s : N.State) (i : N.Inputs) :
  R.v42579 (state s) (inputs i) = Zmod.unsigned (N.v42579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42579 s i)) at 1.
  unfold R.v42579, N.v42579.
  rewrite ?node_42574.
  rewrite ?node_42578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42580 (s : N.State) (i : N.Inputs) :
  R.v42580 (state s) (inputs i) = Zmod.unsigned (N.v42580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42580 s i)) at 1.
  unfold R.v42580, N.v42580.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42581 (s : N.State) (i : N.Inputs) :
  R.v42581 (state s) (inputs i) = Zmod.unsigned (N.v42581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42581 s i)) at 1.
  unfold R.v42581, N.v42581.
  rewrite ?node_10046.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42582 (s : N.State) (i : N.Inputs) :
  R.v42582 (state s) (inputs i) = Zmod.unsigned (N.v42582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42582 s i)) at 1.
  unfold R.v42582, N.v42582.
  unfold R.v6, N.v6.
  rewrite ?node_10042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42583 (s : N.State) (i : N.Inputs) :
  R.v42583 (state s) (inputs i) = Zmod.unsigned (N.v42583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42583 s i)) at 1.
  unfold R.v42583, N.v42583.
  unfold R.v6, N.v6.
  rewrite !state_r1086_nr_5F1086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1086_nr_5F1086 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42584 (s : N.State) (i : N.Inputs) :
  R.v42584 (state s) (inputs i) = Zmod.unsigned (N.v42584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42584 s i)) at 1.
  unfold R.v42584, N.v42584.
  rewrite ?node_42582.
  rewrite ?node_42583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42585 (s : N.State) (i : N.Inputs) :
  R.v42585 (state s) (inputs i) = Zmod.unsigned (N.v42585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42585 s i)) at 1.
  unfold R.v42585, N.v42585.
  unfold R.v16484, N.v16484.
  rewrite ?node_42584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42586 (s : N.State) (i : N.Inputs) :
  R.v42586 (state s) (inputs i) = Zmod.unsigned (N.v42586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42586 s i)) at 1.
  unfold R.v42586, N.v42586.
  rewrite ?node_42581.
  rewrite ?node_42585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42587 (s : N.State) (i : N.Inputs) :
  R.v42587 (state s) (inputs i) = Zmod.unsigned (N.v42587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42587 s i)) at 1.
  unfold R.v42587, N.v42587.
  unfold R.v6, N.v6.
  rewrite ?node_42586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42588 (s : N.State) (i : N.Inputs) :
  R.v42588 (state s) (inputs i) = Zmod.unsigned (N.v42588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42588 s i)) at 1.
  unfold R.v42588, N.v42588.
  rewrite ?node_10047.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42589 (s : N.State) (i : N.Inputs) :
  R.v42589 (state s) (inputs i) = Zmod.unsigned (N.v42589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42589 s i)) at 1.
  unfold R.v42589, N.v42589.
  unfold R.v6, N.v6.
  rewrite ?node_10209.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42590 (s : N.State) (i : N.Inputs) :
  R.v42590 (state s) (inputs i) = Zmod.unsigned (N.v42590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42590 s i)) at 1.
  unfold R.v42590, N.v42590.
  rewrite ?node_42588.
  rewrite ?node_42589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42591 (s : N.State) (i : N.Inputs) :
  R.v42591 (state s) (inputs i) = Zmod.unsigned (N.v42591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42591 s i)) at 1.
  unfold R.v42591, N.v42591.
  rewrite ?node_42587.
  rewrite ?node_42590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42592 (s : N.State) (i : N.Inputs) :
  R.v42592 (state s) (inputs i) = Zmod.unsigned (N.v42592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42592 s i)) at 1.
  unfold R.v42592, N.v42592.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42593 (s : N.State) (i : N.Inputs) :
  R.v42593 (state s) (inputs i) = Zmod.unsigned (N.v42593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42593 s i)) at 1.
  unfold R.v42593, N.v42593.
  rewrite ?node_10054.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42594 (s : N.State) (i : N.Inputs) :
  R.v42594 (state s) (inputs i) = Zmod.unsigned (N.v42594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42594 s i)) at 1.
  unfold R.v42594, N.v42594.
  unfold R.v6, N.v6.
  rewrite ?node_10050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42595 (s : N.State) (i : N.Inputs) :
  R.v42595 (state s) (inputs i) = Zmod.unsigned (N.v42595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42595 s i)) at 1.
  unfold R.v42595, N.v42595.
  unfold R.v6, N.v6.
  rewrite ?node_10047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42596 (s : N.State) (i : N.Inputs) :
  R.v42596 (state s) (inputs i) = Zmod.unsigned (N.v42596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42596 s i)) at 1.
  unfold R.v42596, N.v42596.
  rewrite ?node_42594.
  rewrite ?node_42595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42597 (s : N.State) (i : N.Inputs) :
  R.v42597 (state s) (inputs i) = Zmod.unsigned (N.v42597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42597 s i)) at 1.
  unfold R.v42597, N.v42597.
  unfold R.v16484, N.v16484.
  rewrite ?node_42596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42598 (s : N.State) (i : N.Inputs) :
  R.v42598 (state s) (inputs i) = Zmod.unsigned (N.v42598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42598 s i)) at 1.
  unfold R.v42598, N.v42598.
  rewrite ?node_42593.
  rewrite ?node_42597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42599 (s : N.State) (i : N.Inputs) :
  R.v42599 (state s) (inputs i) = Zmod.unsigned (N.v42599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42599 s i)) at 1.
  unfold R.v42599, N.v42599.
  unfold R.v6, N.v6.
  rewrite ?node_42598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42600 (s : N.State) (i : N.Inputs) :
  R.v42600 (state s) (inputs i) = Zmod.unsigned (N.v42600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42600 s i)) at 1.
  unfold R.v42600, N.v42600.
  rewrite ?node_10055.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42601 (s : N.State) (i : N.Inputs) :
  R.v42601 (state s) (inputs i) = Zmod.unsigned (N.v42601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42601 s i)) at 1.
  unfold R.v42601, N.v42601.
  unfold R.v6, N.v6.
  rewrite ?node_10249.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42602 (s : N.State) (i : N.Inputs) :
  R.v42602 (state s) (inputs i) = Zmod.unsigned (N.v42602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42602 s i)) at 1.
  unfold R.v42602, N.v42602.
  rewrite ?node_42600.
  rewrite ?node_42601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42603 (s : N.State) (i : N.Inputs) :
  R.v42603 (state s) (inputs i) = Zmod.unsigned (N.v42603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42603 s i)) at 1.
  unfold R.v42603, N.v42603.
  rewrite ?node_42599.
  rewrite ?node_42602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42604 (s : N.State) (i : N.Inputs) :
  R.v42604 (state s) (inputs i) = Zmod.unsigned (N.v42604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42604 s i)) at 1.
  unfold R.v42604, N.v42604.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42605 (s : N.State) (i : N.Inputs) :
  R.v42605 (state s) (inputs i) = Zmod.unsigned (N.v42605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42605 s i)) at 1.
  unfold R.v42605, N.v42605.
  rewrite ?node_10074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42606 (s : N.State) (i : N.Inputs) :
  R.v42606 (state s) (inputs i) = Zmod.unsigned (N.v42606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42606 s i)) at 1.
  unfold R.v42606, N.v42606.
  rewrite ?node_10070.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42607 (s : N.State) (i : N.Inputs) :
  R.v42607 (state s) (inputs i) = Zmod.unsigned (N.v42607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42607 s i)) at 1.
  unfold R.v42607, N.v42607.
  rewrite ?node_10066.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42608 (s : N.State) (i : N.Inputs) :
  R.v42608 (state s) (inputs i) = Zmod.unsigned (N.v42608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42608 s i)) at 1.
  unfold R.v42608, N.v42608.
  unfold R.v6, N.v6.
  rewrite ?node_10062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42609 (s : N.State) (i : N.Inputs) :
  R.v42609 (state s) (inputs i) = Zmod.unsigned (N.v42609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42609 s i)) at 1.
  unfold R.v42609, N.v42609.
  unfold R.v6, N.v6.
  rewrite ?node_10059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42610 (s : N.State) (i : N.Inputs) :
  R.v42610 (state s) (inputs i) = Zmod.unsigned (N.v42610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42610 s i)) at 1.
  unfold R.v42610, N.v42610.
  rewrite ?node_42608.
  rewrite ?node_42609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42611 (s : N.State) (i : N.Inputs) :
  R.v42611 (state s) (inputs i) = Zmod.unsigned (N.v42611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42611 s i)) at 1.
  unfold R.v42611, N.v42611.
  unfold R.v16484, N.v16484.
  rewrite ?node_42610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42612 (s : N.State) (i : N.Inputs) :
  R.v42612 (state s) (inputs i) = Zmod.unsigned (N.v42612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42612 s i)) at 1.
  unfold R.v42612, N.v42612.
  rewrite ?node_42605.
  rewrite ?node_42606.
  rewrite ?node_42607.
  rewrite ?node_42611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42613 (s : N.State) (i : N.Inputs) :
  R.v42613 (state s) (inputs i) = Zmod.unsigned (N.v42613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42613 s i)) at 1.
  unfold R.v42613, N.v42613.
  unfold R.v6, N.v6.
  rewrite ?node_42612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42614 (s : N.State) (i : N.Inputs) :
  R.v42614 (state s) (inputs i) = Zmod.unsigned (N.v42614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42614 s i)) at 1.
  unfold R.v42614, N.v42614.
  rewrite ?node_10075.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42615 (s : N.State) (i : N.Inputs) :
  R.v42615 (state s) (inputs i) = Zmod.unsigned (N.v42615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42615 s i)) at 1.
  unfold R.v42615, N.v42615.
  unfold R.v6, N.v6.
  rewrite ?node_10229.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42616 (s : N.State) (i : N.Inputs) :
  R.v42616 (state s) (inputs i) = Zmod.unsigned (N.v42616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42616 s i)) at 1.
  unfold R.v42616, N.v42616.
  unfold R.v6, N.v6.
  rewrite ?node_10258.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42617 (s : N.State) (i : N.Inputs) :
  R.v42617 (state s) (inputs i) = Zmod.unsigned (N.v42617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42617 s i)) at 1.
  unfold R.v42617, N.v42617.
  rewrite ?node_42614.
  rewrite ?node_42615.
  rewrite ?node_42616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42618 (s : N.State) (i : N.Inputs) :
  R.v42618 (state s) (inputs i) = Zmod.unsigned (N.v42618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42618 s i)) at 1.
  unfold R.v42618, N.v42618.
  rewrite ?node_42613.
  rewrite ?node_42617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42619 (s : N.State) (i : N.Inputs) :
  R.v42619 (state s) (inputs i) = Zmod.unsigned (N.v42619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42619 s i)) at 1.
  unfold R.v42619, N.v42619.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42620 (s : N.State) (i : N.Inputs) :
  R.v42620 (state s) (inputs i) = Zmod.unsigned (N.v42620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42620 s i)) at 1.
  unfold R.v42620, N.v42620.
  rewrite ?node_10066.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42621 (s : N.State) (i : N.Inputs) :
  R.v42621 (state s) (inputs i) = Zmod.unsigned (N.v42621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42621 s i)) at 1.
  unfold R.v42621, N.v42621.
  unfold R.v6, N.v6.
  rewrite ?node_10062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42622 (s : N.State) (i : N.Inputs) :
  R.v42622 (state s) (inputs i) = Zmod.unsigned (N.v42622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42622 s i)) at 1.
  unfold R.v42622, N.v42622.
  unfold R.v6, N.v6.
  rewrite ?node_10059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42623 (s : N.State) (i : N.Inputs) :
  R.v42623 (state s) (inputs i) = Zmod.unsigned (N.v42623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42623 s i)) at 1.
  unfold R.v42623, N.v42623.
  rewrite ?node_42621.
  rewrite ?node_42622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42624 (s : N.State) (i : N.Inputs) :
  R.v42624 (state s) (inputs i) = Zmod.unsigned (N.v42624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42624 s i)) at 1.
  unfold R.v42624, N.v42624.
  unfold R.v16484, N.v16484.
  rewrite ?node_42623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42625 (s : N.State) (i : N.Inputs) :
  R.v42625 (state s) (inputs i) = Zmod.unsigned (N.v42625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42625 s i)) at 1.
  unfold R.v42625, N.v42625.
  rewrite ?node_42620.
  rewrite ?node_42624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42626 (s : N.State) (i : N.Inputs) :
  R.v42626 (state s) (inputs i) = Zmod.unsigned (N.v42626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42626 s i)) at 1.
  unfold R.v42626, N.v42626.
  unfold R.v6, N.v6.
  rewrite ?node_42625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42627 (s : N.State) (i : N.Inputs) :
  R.v42627 (state s) (inputs i) = Zmod.unsigned (N.v42627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42627 s i)) at 1.
  unfold R.v42627, N.v42627.
  rewrite ?node_10067.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42628 (s : N.State) (i : N.Inputs) :
  R.v42628 (state s) (inputs i) = Zmod.unsigned (N.v42628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42628 s i)) at 1.
  unfold R.v42628, N.v42628.
  unfold R.v6, N.v6.
  rewrite ?node_10229.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42629 (s : N.State) (i : N.Inputs) :
  R.v42629 (state s) (inputs i) = Zmod.unsigned (N.v42629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42629 s i)) at 1.
  unfold R.v42629, N.v42629.
  rewrite ?node_42627.
  rewrite ?node_42628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42630 (s : N.State) (i : N.Inputs) :
  R.v42630 (state s) (inputs i) = Zmod.unsigned (N.v42630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42630 s i)) at 1.
  unfold R.v42630, N.v42630.
  rewrite ?node_42626.
  rewrite ?node_42629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42631 (s : N.State) (i : N.Inputs) :
  R.v42631 (state s) (inputs i) = Zmod.unsigned (N.v42631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42631 s i)) at 1.
  unfold R.v42631, N.v42631.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42632 (s : N.State) (i : N.Inputs) :
  R.v42632 (state s) (inputs i) = Zmod.unsigned (N.v42632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42632 s i)) at 1.
  unfold R.v42632, N.v42632.
  rewrite ?node_10074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42633 (s : N.State) (i : N.Inputs) :
  R.v42633 (state s) (inputs i) = Zmod.unsigned (N.v42633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42633 s i)) at 1.
  unfold R.v42633, N.v42633.
  unfold R.v6, N.v6.
  rewrite ?node_10070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42634 (s : N.State) (i : N.Inputs) :
  R.v42634 (state s) (inputs i) = Zmod.unsigned (N.v42634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42634 s i)) at 1.
  unfold R.v42634, N.v42634.
  unfold R.v6, N.v6.
  rewrite ?node_10067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42635 (s : N.State) (i : N.Inputs) :
  R.v42635 (state s) (inputs i) = Zmod.unsigned (N.v42635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42635 s i)) at 1.
  unfold R.v42635, N.v42635.
  rewrite ?node_42633.
  rewrite ?node_42634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42636 (s : N.State) (i : N.Inputs) :
  R.v42636 (state s) (inputs i) = Zmod.unsigned (N.v42636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42636 s i)) at 1.
  unfold R.v42636, N.v42636.
  unfold R.v16484, N.v16484.
  rewrite ?node_42635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42637 (s : N.State) (i : N.Inputs) :
  R.v42637 (state s) (inputs i) = Zmod.unsigned (N.v42637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42637 s i)) at 1.
  unfold R.v42637, N.v42637.
  rewrite ?node_42632.
  rewrite ?node_42636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42638 (s : N.State) (i : N.Inputs) :
  R.v42638 (state s) (inputs i) = Zmod.unsigned (N.v42638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42638 s i)) at 1.
  unfold R.v42638, N.v42638.
  unfold R.v6, N.v6.
  rewrite ?node_42637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42639 (s : N.State) (i : N.Inputs) :
  R.v42639 (state s) (inputs i) = Zmod.unsigned (N.v42639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42639 s i)) at 1.
  unfold R.v42639, N.v42639.
  rewrite ?node_10075.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42640 (s : N.State) (i : N.Inputs) :
  R.v42640 (state s) (inputs i) = Zmod.unsigned (N.v42640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42640 s i)) at 1.
  unfold R.v42640, N.v42640.
  unfold R.v6, N.v6.
  rewrite ?node_10258.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42641 (s : N.State) (i : N.Inputs) :
  R.v42641 (state s) (inputs i) = Zmod.unsigned (N.v42641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42641 s i)) at 1.
  unfold R.v42641, N.v42641.
  rewrite ?node_42639.
  rewrite ?node_42640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42642 (s : N.State) (i : N.Inputs) :
  R.v42642 (state s) (inputs i) = Zmod.unsigned (N.v42642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42642 s i)) at 1.
  unfold R.v42642, N.v42642.
  rewrite ?node_42638.
  rewrite ?node_42641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42643 (s : N.State) (i : N.Inputs) :
  R.v42643 (state s) (inputs i) = Zmod.unsigned (N.v42643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42643 s i)) at 1.
  unfold R.v42643, N.v42643.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42644 (s : N.State) (i : N.Inputs) :
  R.v42644 (state s) (inputs i) = Zmod.unsigned (N.v42644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42644 s i)) at 1.
  unfold R.v42644, N.v42644.
  rewrite ?node_10157.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42645 (s : N.State) (i : N.Inputs) :
  R.v42645 (state s) (inputs i) = Zmod.unsigned (N.v42645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42645 s i)) at 1.
  unfold R.v42645, N.v42645.
  rewrite ?node_10153.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42646 (s : N.State) (i : N.Inputs) :
  R.v42646 (state s) (inputs i) = Zmod.unsigned (N.v42646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42646 s i)) at 1.
  unfold R.v42646, N.v42646.
  rewrite ?node_10145.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42647 (s : N.State) (i : N.Inputs) :
  R.v42647 (state s) (inputs i) = Zmod.unsigned (N.v42647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42647 s i)) at 1.
  unfold R.v42647, N.v42647.
  unfold R.v6, N.v6.
  rewrite ?node_10137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42648 (s : N.State) (i : N.Inputs) :
  R.v42648 (state s) (inputs i) = Zmod.unsigned (N.v42648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42648 s i)) at 1.
  unfold R.v42648, N.v42648.
  unfold R.v6, N.v6.
  rewrite ?node_10130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42649 (s : N.State) (i : N.Inputs) :
  R.v42649 (state s) (inputs i) = Zmod.unsigned (N.v42649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42649 s i)) at 1.
  unfold R.v42649, N.v42649.
  rewrite ?node_42647.
  rewrite ?node_42648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42650 (s : N.State) (i : N.Inputs) :
  R.v42650 (state s) (inputs i) = Zmod.unsigned (N.v42650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42650 s i)) at 1.
  unfold R.v42650, N.v42650.
  unfold R.v16484, N.v16484.
  rewrite ?node_42649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42651 (s : N.State) (i : N.Inputs) :
  R.v42651 (state s) (inputs i) = Zmod.unsigned (N.v42651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42651 s i)) at 1.
  unfold R.v42651, N.v42651.
  rewrite ?node_42644.
  rewrite ?node_42645.
  rewrite ?node_42646.
  rewrite ?node_42650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42652 (s : N.State) (i : N.Inputs) :
  R.v42652 (state s) (inputs i) = Zmod.unsigned (N.v42652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42652 s i)) at 1.
  unfold R.v42652, N.v42652.
  unfold R.v6, N.v6.
  rewrite ?node_42651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42653 (s : N.State) (i : N.Inputs) :
  R.v42653 (state s) (inputs i) = Zmod.unsigned (N.v42653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42653 s i)) at 1.
  unfold R.v42653, N.v42653.
  rewrite ?node_10158.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42654 (s : N.State) (i : N.Inputs) :
  R.v42654 (state s) (inputs i) = Zmod.unsigned (N.v42654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42654 s i)) at 1.
  unfold R.v42654, N.v42654.
  unfold R.v6, N.v6.
  rewrite ?node_10314.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42655 (s : N.State) (i : N.Inputs) :
  R.v42655 (state s) (inputs i) = Zmod.unsigned (N.v42655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42655 s i)) at 1.
  unfold R.v42655, N.v42655.
  unfold R.v6, N.v6.
  rewrite ?node_10399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42656 (s : N.State) (i : N.Inputs) :
  R.v42656 (state s) (inputs i) = Zmod.unsigned (N.v42656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42656 s i)) at 1.
  unfold R.v42656, N.v42656.
  rewrite ?node_42653.
  rewrite ?node_42654.
  rewrite ?node_42655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42657 (s : N.State) (i : N.Inputs) :
  R.v42657 (state s) (inputs i) = Zmod.unsigned (N.v42657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42657 s i)) at 1.
  unfold R.v42657, N.v42657.
  rewrite ?node_42652.
  rewrite ?node_42656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42658 (s : N.State) (i : N.Inputs) :
  R.v42658 (state s) (inputs i) = Zmod.unsigned (N.v42658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42658 s i)) at 1.
  unfold R.v42658, N.v42658.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42659 (s : N.State) (i : N.Inputs) :
  R.v42659 (state s) (inputs i) = Zmod.unsigned (N.v42659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42659 s i)) at 1.
  unfold R.v42659, N.v42659.
  rewrite ?node_10145.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42660 (s : N.State) (i : N.Inputs) :
  R.v42660 (state s) (inputs i) = Zmod.unsigned (N.v42660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42660 s i)) at 1.
  unfold R.v42660, N.v42660.
  unfold R.v6, N.v6.
  rewrite ?node_10137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42661 (s : N.State) (i : N.Inputs) :
  R.v42661 (state s) (inputs i) = Zmod.unsigned (N.v42661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42661 s i)) at 1.
  unfold R.v42661, N.v42661.
  unfold R.v6, N.v6.
  rewrite ?node_10130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42662 (s : N.State) (i : N.Inputs) :
  R.v42662 (state s) (inputs i) = Zmod.unsigned (N.v42662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42662 s i)) at 1.
  unfold R.v42662, N.v42662.
  rewrite ?node_42660.
  rewrite ?node_42661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42663 (s : N.State) (i : N.Inputs) :
  R.v42663 (state s) (inputs i) = Zmod.unsigned (N.v42663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42663 s i)) at 1.
  unfold R.v42663, N.v42663.
  unfold R.v16484, N.v16484.
  rewrite ?node_42662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42664 (s : N.State) (i : N.Inputs) :
  R.v42664 (state s) (inputs i) = Zmod.unsigned (N.v42664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42664 s i)) at 1.
  unfold R.v42664, N.v42664.
  rewrite ?node_42659.
  rewrite ?node_42663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42665 (s : N.State) (i : N.Inputs) :
  R.v42665 (state s) (inputs i) = Zmod.unsigned (N.v42665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42665 s i)) at 1.
  unfold R.v42665, N.v42665.
  unfold R.v6, N.v6.
  rewrite ?node_42664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42666 (s : N.State) (i : N.Inputs) :
  R.v42666 (state s) (inputs i) = Zmod.unsigned (N.v42666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42666 s i)) at 1.
  unfold R.v42666, N.v42666.
  rewrite ?node_10146.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42667 (s : N.State) (i : N.Inputs) :
  R.v42667 (state s) (inputs i) = Zmod.unsigned (N.v42667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42667 s i)) at 1.
  unfold R.v42667, N.v42667.
  unfold R.v6, N.v6.
  rewrite ?node_10314.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42668 (s : N.State) (i : N.Inputs) :
  R.v42668 (state s) (inputs i) = Zmod.unsigned (N.v42668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42668 s i)) at 1.
  unfold R.v42668, N.v42668.
  rewrite ?node_42666.
  rewrite ?node_42667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42669 (s : N.State) (i : N.Inputs) :
  R.v42669 (state s) (inputs i) = Zmod.unsigned (N.v42669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42669 s i)) at 1.
  unfold R.v42669, N.v42669.
  rewrite ?node_42665.
  rewrite ?node_42668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42670 (s : N.State) (i : N.Inputs) :
  R.v42670 (state s) (inputs i) = Zmod.unsigned (N.v42670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42670 s i)) at 1.
  unfold R.v42670, N.v42670.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42671 (s : N.State) (i : N.Inputs) :
  R.v42671 (state s) (inputs i) = Zmod.unsigned (N.v42671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42671 s i)) at 1.
  unfold R.v42671, N.v42671.
  rewrite ?node_10157.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42672 (s : N.State) (i : N.Inputs) :
  R.v42672 (state s) (inputs i) = Zmod.unsigned (N.v42672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42672 s i)) at 1.
  unfold R.v42672, N.v42672.
  unfold R.v6, N.v6.
  rewrite ?node_10153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42673 (s : N.State) (i : N.Inputs) :
  R.v42673 (state s) (inputs i) = Zmod.unsigned (N.v42673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42673 s i)) at 1.
  unfold R.v42673, N.v42673.
  unfold R.v6, N.v6.
  rewrite ?node_10146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42674 (s : N.State) (i : N.Inputs) :
  R.v42674 (state s) (inputs i) = Zmod.unsigned (N.v42674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42674 s i)) at 1.
  unfold R.v42674, N.v42674.
  rewrite ?node_42672.
  rewrite ?node_42673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42675 (s : N.State) (i : N.Inputs) :
  R.v42675 (state s) (inputs i) = Zmod.unsigned (N.v42675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42675 s i)) at 1.
  unfold R.v42675, N.v42675.
  unfold R.v16484, N.v16484.
  rewrite ?node_42674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42676 (s : N.State) (i : N.Inputs) :
  R.v42676 (state s) (inputs i) = Zmod.unsigned (N.v42676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42676 s i)) at 1.
  unfold R.v42676, N.v42676.
  rewrite ?node_42671.
  rewrite ?node_42675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42677 (s : N.State) (i : N.Inputs) :
  R.v42677 (state s) (inputs i) = Zmod.unsigned (N.v42677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42677 s i)) at 1.
  unfold R.v42677, N.v42677.
  unfold R.v6, N.v6.
  rewrite ?node_42676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42678 (s : N.State) (i : N.Inputs) :
  R.v42678 (state s) (inputs i) = Zmod.unsigned (N.v42678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42678 s i)) at 1.
  unfold R.v42678, N.v42678.
  rewrite ?node_10158.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42679 (s : N.State) (i : N.Inputs) :
  R.v42679 (state s) (inputs i) = Zmod.unsigned (N.v42679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42679 s i)) at 1.
  unfold R.v42679, N.v42679.
  unfold R.v6, N.v6.
  rewrite ?node_10399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42680 (s : N.State) (i : N.Inputs) :
  R.v42680 (state s) (inputs i) = Zmod.unsigned (N.v42680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42680 s i)) at 1.
  unfold R.v42680, N.v42680.
  rewrite ?node_42678.
  rewrite ?node_42679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42681 (s : N.State) (i : N.Inputs) :
  R.v42681 (state s) (inputs i) = Zmod.unsigned (N.v42681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42681 s i)) at 1.
  unfold R.v42681, N.v42681.
  rewrite ?node_42677.
  rewrite ?node_42680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42682 (s : N.State) (i : N.Inputs) :
  R.v42682 (state s) (inputs i) = Zmod.unsigned (N.v42682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42682 s i)) at 1.
  unfold R.v42682, N.v42682.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42683 (s : N.State) (i : N.Inputs) :
  R.v42683 (state s) (inputs i) = Zmod.unsigned (N.v42683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42683 s i)) at 1.
  unfold R.v42683, N.v42683.
  rewrite ?node_10192.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42684 (s : N.State) (i : N.Inputs) :
  R.v42684 (state s) (inputs i) = Zmod.unsigned (N.v42684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42684 s i)) at 1.
  unfold R.v42684, N.v42684.
  rewrite ?node_10188.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42685 (s : N.State) (i : N.Inputs) :
  R.v42685 (state s) (inputs i) = Zmod.unsigned (N.v42685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42685 s i)) at 1.
  unfold R.v42685, N.v42685.
  rewrite ?node_10180.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42686 (s : N.State) (i : N.Inputs) :
  R.v42686 (state s) (inputs i) = Zmod.unsigned (N.v42686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42686 s i)) at 1.
  unfold R.v42686, N.v42686.
  unfold R.v6, N.v6.
  rewrite ?node_10172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42687 (s : N.State) (i : N.Inputs) :
  R.v42687 (state s) (inputs i) = Zmod.unsigned (N.v42687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42687 s i)) at 1.
  unfold R.v42687, N.v42687.
  unfold R.v6, N.v6.
  rewrite ?node_10165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42688 (s : N.State) (i : N.Inputs) :
  R.v42688 (state s) (inputs i) = Zmod.unsigned (N.v42688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42688 s i)) at 1.
  unfold R.v42688, N.v42688.
  rewrite ?node_42686.
  rewrite ?node_42687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42689 (s : N.State) (i : N.Inputs) :
  R.v42689 (state s) (inputs i) = Zmod.unsigned (N.v42689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42689 s i)) at 1.
  unfold R.v42689, N.v42689.
  unfold R.v16484, N.v16484.
  rewrite ?node_42688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42690 (s : N.State) (i : N.Inputs) :
  R.v42690 (state s) (inputs i) = Zmod.unsigned (N.v42690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42690 s i)) at 1.
  unfold R.v42690, N.v42690.
  rewrite ?node_42683.
  rewrite ?node_42684.
  rewrite ?node_42685.
  rewrite ?node_42689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42691 (s : N.State) (i : N.Inputs) :
  R.v42691 (state s) (inputs i) = Zmod.unsigned (N.v42691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42691 s i)) at 1.
  unfold R.v42691, N.v42691.
  unfold R.v6, N.v6.
  rewrite ?node_42690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42692 (s : N.State) (i : N.Inputs) :
  R.v42692 (state s) (inputs i) = Zmod.unsigned (N.v42692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42692 s i)) at 1.
  unfold R.v42692, N.v42692.
  rewrite ?node_10193.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42693 (s : N.State) (i : N.Inputs) :
  R.v42693 (state s) (inputs i) = Zmod.unsigned (N.v42693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42693 s i)) at 1.
  unfold R.v42693, N.v42693.
  unfold R.v6, N.v6.
  rewrite ?node_10349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42694 (s : N.State) (i : N.Inputs) :
  R.v42694 (state s) (inputs i) = Zmod.unsigned (N.v42694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42694 s i)) at 1.
  unfold R.v42694, N.v42694.
  unfold R.v6, N.v6.
  rewrite ?node_10403.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42695 (s : N.State) (i : N.Inputs) :
  R.v42695 (state s) (inputs i) = Zmod.unsigned (N.v42695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42695 s i)) at 1.
  unfold R.v42695, N.v42695.
  rewrite ?node_42692.
  rewrite ?node_42693.
  rewrite ?node_42694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42696 (s : N.State) (i : N.Inputs) :
  R.v42696 (state s) (inputs i) = Zmod.unsigned (N.v42696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42696 s i)) at 1.
  unfold R.v42696, N.v42696.
  rewrite ?node_42691.
  rewrite ?node_42695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42697 (s : N.State) (i : N.Inputs) :
  R.v42697 (state s) (inputs i) = Zmod.unsigned (N.v42697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42697 s i)) at 1.
  unfold R.v42697, N.v42697.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42698 (s : N.State) (i : N.Inputs) :
  R.v42698 (state s) (inputs i) = Zmod.unsigned (N.v42698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42698 s i)) at 1.
  unfold R.v42698, N.v42698.
  rewrite ?node_10180.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42699 (s : N.State) (i : N.Inputs) :
  R.v42699 (state s) (inputs i) = Zmod.unsigned (N.v42699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42699 s i)) at 1.
  unfold R.v42699, N.v42699.
  unfold R.v6, N.v6.
  rewrite ?node_10172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42700 (s : N.State) (i : N.Inputs) :
  R.v42700 (state s) (inputs i) = Zmod.unsigned (N.v42700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42700 s i)) at 1.
  unfold R.v42700, N.v42700.
  unfold R.v6, N.v6.
  rewrite ?node_10165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42701 (s : N.State) (i : N.Inputs) :
  R.v42701 (state s) (inputs i) = Zmod.unsigned (N.v42701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42701 s i)) at 1.
  unfold R.v42701, N.v42701.
  rewrite ?node_42699.
  rewrite ?node_42700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42702 (s : N.State) (i : N.Inputs) :
  R.v42702 (state s) (inputs i) = Zmod.unsigned (N.v42702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42702 s i)) at 1.
  unfold R.v42702, N.v42702.
  unfold R.v16484, N.v16484.
  rewrite ?node_42701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42703 (s : N.State) (i : N.Inputs) :
  R.v42703 (state s) (inputs i) = Zmod.unsigned (N.v42703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42703 s i)) at 1.
  unfold R.v42703, N.v42703.
  rewrite ?node_42698.
  rewrite ?node_42702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42704 (s : N.State) (i : N.Inputs) :
  R.v42704 (state s) (inputs i) = Zmod.unsigned (N.v42704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42704 s i)) at 1.
  unfold R.v42704, N.v42704.
  unfold R.v6, N.v6.
  rewrite ?node_42703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42705 (s : N.State) (i : N.Inputs) :
  R.v42705 (state s) (inputs i) = Zmod.unsigned (N.v42705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42705 s i)) at 1.
  unfold R.v42705, N.v42705.
  rewrite ?node_10181.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42706 (s : N.State) (i : N.Inputs) :
  R.v42706 (state s) (inputs i) = Zmod.unsigned (N.v42706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42706 s i)) at 1.
  unfold R.v42706, N.v42706.
  unfold R.v6, N.v6.
  rewrite ?node_10349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42707 (s : N.State) (i : N.Inputs) :
  R.v42707 (state s) (inputs i) = Zmod.unsigned (N.v42707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42707 s i)) at 1.
  unfold R.v42707, N.v42707.
  rewrite ?node_42705.
  rewrite ?node_42706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42708 (s : N.State) (i : N.Inputs) :
  R.v42708 (state s) (inputs i) = Zmod.unsigned (N.v42708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42708 s i)) at 1.
  unfold R.v42708, N.v42708.
  rewrite ?node_42704.
  rewrite ?node_42707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42709 (s : N.State) (i : N.Inputs) :
  R.v42709 (state s) (inputs i) = Zmod.unsigned (N.v42709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42709 s i)) at 1.
  unfold R.v42709, N.v42709.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42710 (s : N.State) (i : N.Inputs) :
  R.v42710 (state s) (inputs i) = Zmod.unsigned (N.v42710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42710 s i)) at 1.
  unfold R.v42710, N.v42710.
  rewrite ?node_10192.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42711 (s : N.State) (i : N.Inputs) :
  R.v42711 (state s) (inputs i) = Zmod.unsigned (N.v42711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42711 s i)) at 1.
  unfold R.v42711, N.v42711.
  unfold R.v6, N.v6.
  rewrite ?node_10188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42712 (s : N.State) (i : N.Inputs) :
  R.v42712 (state s) (inputs i) = Zmod.unsigned (N.v42712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42712 s i)) at 1.
  unfold R.v42712, N.v42712.
  unfold R.v6, N.v6.
  rewrite ?node_10181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42713 (s : N.State) (i : N.Inputs) :
  R.v42713 (state s) (inputs i) = Zmod.unsigned (N.v42713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42713 s i)) at 1.
  unfold R.v42713, N.v42713.
  rewrite ?node_42711.
  rewrite ?node_42712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42714 (s : N.State) (i : N.Inputs) :
  R.v42714 (state s) (inputs i) = Zmod.unsigned (N.v42714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42714 s i)) at 1.
  unfold R.v42714, N.v42714.
  unfold R.v16484, N.v16484.
  rewrite ?node_42713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42715 (s : N.State) (i : N.Inputs) :
  R.v42715 (state s) (inputs i) = Zmod.unsigned (N.v42715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42715 s i)) at 1.
  unfold R.v42715, N.v42715.
  rewrite ?node_42710.
  rewrite ?node_42714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42716 (s : N.State) (i : N.Inputs) :
  R.v42716 (state s) (inputs i) = Zmod.unsigned (N.v42716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42716 s i)) at 1.
  unfold R.v42716, N.v42716.
  unfold R.v6, N.v6.
  rewrite ?node_42715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42717 (s : N.State) (i : N.Inputs) :
  R.v42717 (state s) (inputs i) = Zmod.unsigned (N.v42717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42717 s i)) at 1.
  unfold R.v42717, N.v42717.
  rewrite ?node_10193.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42718 (s : N.State) (i : N.Inputs) :
  R.v42718 (state s) (inputs i) = Zmod.unsigned (N.v42718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42718 s i)) at 1.
  unfold R.v42718, N.v42718.
  unfold R.v6, N.v6.
  rewrite ?node_10403.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42719 (s : N.State) (i : N.Inputs) :
  R.v42719 (state s) (inputs i) = Zmod.unsigned (N.v42719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42719 s i)) at 1.
  unfold R.v42719, N.v42719.
  rewrite ?node_42717.
  rewrite ?node_42718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42720 (s : N.State) (i : N.Inputs) :
  R.v42720 (state s) (inputs i) = Zmod.unsigned (N.v42720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42720 s i)) at 1.
  unfold R.v42720, N.v42720.
  rewrite ?node_42716.
  rewrite ?node_42719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42721 (s : N.State) (i : N.Inputs) :
  R.v42721 (state s) (inputs i) = Zmod.unsigned (N.v42721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42721 s i)) at 1.
  unfold R.v42721, N.v42721.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42722 (s : N.State) (i : N.Inputs) :
  R.v42722 (state s) (inputs i) = Zmod.unsigned (N.v42722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42722 s i)) at 1.
  unfold R.v42722, N.v42722.
  rewrite ?node_10209.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42723 (s : N.State) (i : N.Inputs) :
  R.v42723 (state s) (inputs i) = Zmod.unsigned (N.v42723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42723 s i)) at 1.
  unfold R.v42723, N.v42723.
  rewrite ?node_10205.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42724 (s : N.State) (i : N.Inputs) :
  R.v42724 (state s) (inputs i) = Zmod.unsigned (N.v42724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42724 s i)) at 1.
  unfold R.v42724, N.v42724.
  rewrite ?node_10201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42725 (s : N.State) (i : N.Inputs) :
  R.v42725 (state s) (inputs i) = Zmod.unsigned (N.v42725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42725 s i)) at 1.
  unfold R.v42725, N.v42725.
  unfold R.v6, N.v6.
  rewrite ?node_10197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42726 (s : N.State) (i : N.Inputs) :
  R.v42726 (state s) (inputs i) = Zmod.unsigned (N.v42726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42726 s i)) at 1.
  unfold R.v42726, N.v42726.
  unfold R.v6, N.v6.
  rewrite !state_r1119_nr_5F1119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1119_nr_5F1119 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42727 (s : N.State) (i : N.Inputs) :
  R.v42727 (state s) (inputs i) = Zmod.unsigned (N.v42727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42727 s i)) at 1.
  unfold R.v42727, N.v42727.
  rewrite ?node_42725.
  rewrite ?node_42726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42728 (s : N.State) (i : N.Inputs) :
  R.v42728 (state s) (inputs i) = Zmod.unsigned (N.v42728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42728 s i)) at 1.
  unfold R.v42728, N.v42728.
  unfold R.v16484, N.v16484.
  rewrite ?node_42727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42729 (s : N.State) (i : N.Inputs) :
  R.v42729 (state s) (inputs i) = Zmod.unsigned (N.v42729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42729 s i)) at 1.
  unfold R.v42729, N.v42729.
  rewrite ?node_42722.
  rewrite ?node_42723.
  rewrite ?node_42724.
  rewrite ?node_42728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42730 (s : N.State) (i : N.Inputs) :
  R.v42730 (state s) (inputs i) = Zmod.unsigned (N.v42730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42730 s i)) at 1.
  unfold R.v42730, N.v42730.
  unfold R.v6, N.v6.
  rewrite ?node_42729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42731 (s : N.State) (i : N.Inputs) :
  R.v42731 (state s) (inputs i) = Zmod.unsigned (N.v42731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42731 s i)) at 1.
  unfold R.v42731, N.v42731.
  rewrite ?node_10210.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42732 (s : N.State) (i : N.Inputs) :
  R.v42732 (state s) (inputs i) = Zmod.unsigned (N.v42732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42732 s i)) at 1.
  unfold R.v42732, N.v42732.
  unfold R.v6, N.v6.
  rewrite ?node_10367.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42733 (s : N.State) (i : N.Inputs) :
  R.v42733 (state s) (inputs i) = Zmod.unsigned (N.v42733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42733 s i)) at 1.
  unfold R.v42733, N.v42733.
  unfold R.v6, N.v6.
  rewrite ?node_10407.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42734 (s : N.State) (i : N.Inputs) :
  R.v42734 (state s) (inputs i) = Zmod.unsigned (N.v42734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42734 s i)) at 1.
  unfold R.v42734, N.v42734.
  rewrite ?node_42731.
  rewrite ?node_42732.
  rewrite ?node_42733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42735 (s : N.State) (i : N.Inputs) :
  R.v42735 (state s) (inputs i) = Zmod.unsigned (N.v42735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42735 s i)) at 1.
  unfold R.v42735, N.v42735.
  rewrite ?node_42730.
  rewrite ?node_42734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42736 (s : N.State) (i : N.Inputs) :
  R.v42736 (state s) (inputs i) = Zmod.unsigned (N.v42736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42736 s i)) at 1.
  unfold R.v42736, N.v42736.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42737 (s : N.State) (i : N.Inputs) :
  R.v42737 (state s) (inputs i) = Zmod.unsigned (N.v42737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42737 s i)) at 1.
  unfold R.v42737, N.v42737.
  rewrite ?node_10201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42738 (s : N.State) (i : N.Inputs) :
  R.v42738 (state s) (inputs i) = Zmod.unsigned (N.v42738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42738 s i)) at 1.
  unfold R.v42738, N.v42738.
  unfold R.v6, N.v6.
  rewrite ?node_10197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42739 (s : N.State) (i : N.Inputs) :
  R.v42739 (state s) (inputs i) = Zmod.unsigned (N.v42739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42739 s i)) at 1.
  unfold R.v42739, N.v42739.
  unfold R.v6, N.v6.
  rewrite !state_r1119_nr_5F1119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1119_nr_5F1119 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42740 (s : N.State) (i : N.Inputs) :
  R.v42740 (state s) (inputs i) = Zmod.unsigned (N.v42740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42740 s i)) at 1.
  unfold R.v42740, N.v42740.
  rewrite ?node_42738.
  rewrite ?node_42739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42741 (s : N.State) (i : N.Inputs) :
  R.v42741 (state s) (inputs i) = Zmod.unsigned (N.v42741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42741 s i)) at 1.
  unfold R.v42741, N.v42741.
  unfold R.v16484, N.v16484.
  rewrite ?node_42740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42742 (s : N.State) (i : N.Inputs) :
  R.v42742 (state s) (inputs i) = Zmod.unsigned (N.v42742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42742 s i)) at 1.
  unfold R.v42742, N.v42742.
  rewrite ?node_42737.
  rewrite ?node_42741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42743 (s : N.State) (i : N.Inputs) :
  R.v42743 (state s) (inputs i) = Zmod.unsigned (N.v42743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42743 s i)) at 1.
  unfold R.v42743, N.v42743.
  unfold R.v6, N.v6.
  rewrite ?node_42742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42744 (s : N.State) (i : N.Inputs) :
  R.v42744 (state s) (inputs i) = Zmod.unsigned (N.v42744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42744 s i)) at 1.
  unfold R.v42744, N.v42744.
  rewrite ?node_10202.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42745 (s : N.State) (i : N.Inputs) :
  R.v42745 (state s) (inputs i) = Zmod.unsigned (N.v42745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42745 s i)) at 1.
  unfold R.v42745, N.v42745.
  unfold R.v6, N.v6.
  rewrite ?node_10367.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42746 (s : N.State) (i : N.Inputs) :
  R.v42746 (state s) (inputs i) = Zmod.unsigned (N.v42746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42746 s i)) at 1.
  unfold R.v42746, N.v42746.
  rewrite ?node_42744.
  rewrite ?node_42745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42747 (s : N.State) (i : N.Inputs) :
  R.v42747 (state s) (inputs i) = Zmod.unsigned (N.v42747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42747 s i)) at 1.
  unfold R.v42747, N.v42747.
  rewrite ?node_42743.
  rewrite ?node_42746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42748 (s : N.State) (i : N.Inputs) :
  R.v42748 (state s) (inputs i) = Zmod.unsigned (N.v42748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42748 s i)) at 1.
  unfold R.v42748, N.v42748.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42749 (s : N.State) (i : N.Inputs) :
  R.v42749 (state s) (inputs i) = Zmod.unsigned (N.v42749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42749 s i)) at 1.
  unfold R.v42749, N.v42749.
  rewrite ?node_10209.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42750 (s : N.State) (i : N.Inputs) :
  R.v42750 (state s) (inputs i) = Zmod.unsigned (N.v42750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42750 s i)) at 1.
  unfold R.v42750, N.v42750.
  unfold R.v6, N.v6.
  rewrite ?node_10205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42751 (s : N.State) (i : N.Inputs) :
  R.v42751 (state s) (inputs i) = Zmod.unsigned (N.v42751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42751 s i)) at 1.
  unfold R.v42751, N.v42751.
  unfold R.v6, N.v6.
  rewrite ?node_10202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42752 (s : N.State) (i : N.Inputs) :
  R.v42752 (state s) (inputs i) = Zmod.unsigned (N.v42752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42752 s i)) at 1.
  unfold R.v42752, N.v42752.
  rewrite ?node_42750.
  rewrite ?node_42751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42753 (s : N.State) (i : N.Inputs) :
  R.v42753 (state s) (inputs i) = Zmod.unsigned (N.v42753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42753 s i)) at 1.
  unfold R.v42753, N.v42753.
  unfold R.v16484, N.v16484.
  rewrite ?node_42752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42754 (s : N.State) (i : N.Inputs) :
  R.v42754 (state s) (inputs i) = Zmod.unsigned (N.v42754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42754 s i)) at 1.
  unfold R.v42754, N.v42754.
  rewrite ?node_42749.
  rewrite ?node_42753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42755 (s : N.State) (i : N.Inputs) :
  R.v42755 (state s) (inputs i) = Zmod.unsigned (N.v42755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42755 s i)) at 1.
  unfold R.v42755, N.v42755.
  unfold R.v6, N.v6.
  rewrite ?node_42754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42756 (s : N.State) (i : N.Inputs) :
  R.v42756 (state s) (inputs i) = Zmod.unsigned (N.v42756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42756 s i)) at 1.
  unfold R.v42756, N.v42756.
  rewrite ?node_10210.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42757 (s : N.State) (i : N.Inputs) :
  R.v42757 (state s) (inputs i) = Zmod.unsigned (N.v42757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42757 s i)) at 1.
  unfold R.v42757, N.v42757.
  unfold R.v6, N.v6.
  rewrite ?node_10407.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42758 (s : N.State) (i : N.Inputs) :
  R.v42758 (state s) (inputs i) = Zmod.unsigned (N.v42758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42758 s i)) at 1.
  unfold R.v42758, N.v42758.
  rewrite ?node_42756.
  rewrite ?node_42757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42759 (s : N.State) (i : N.Inputs) :
  R.v42759 (state s) (inputs i) = Zmod.unsigned (N.v42759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42759 s i)) at 1.
  unfold R.v42759, N.v42759.
  rewrite ?node_42755.
  rewrite ?node_42758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42760 (s : N.State) (i : N.Inputs) :
  R.v42760 (state s) (inputs i) = Zmod.unsigned (N.v42760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42760 s i)) at 1.
  unfold R.v42760, N.v42760.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42761 (s : N.State) (i : N.Inputs) :
  R.v42761 (state s) (inputs i) = Zmod.unsigned (N.v42761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42761 s i)) at 1.
  unfold R.v42761, N.v42761.
  rewrite ?node_10229.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42762 (s : N.State) (i : N.Inputs) :
  R.v42762 (state s) (inputs i) = Zmod.unsigned (N.v42762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42762 s i)) at 1.
  unfold R.v42762, N.v42762.
  rewrite ?node_10225.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42763 (s : N.State) (i : N.Inputs) :
  R.v42763 (state s) (inputs i) = Zmod.unsigned (N.v42763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42763 s i)) at 1.
  unfold R.v42763, N.v42763.
  rewrite ?node_10221.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42764 (s : N.State) (i : N.Inputs) :
  R.v42764 (state s) (inputs i) = Zmod.unsigned (N.v42764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42764 s i)) at 1.
  unfold R.v42764, N.v42764.
  unfold R.v6, N.v6.
  rewrite ?node_10217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42765 (s : N.State) (i : N.Inputs) :
  R.v42765 (state s) (inputs i) = Zmod.unsigned (N.v42765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42765 s i)) at 1.
  unfold R.v42765, N.v42765.
  unfold R.v6, N.v6.
  rewrite ?node_10214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42766 (s : N.State) (i : N.Inputs) :
  R.v42766 (state s) (inputs i) = Zmod.unsigned (N.v42766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42766 s i)) at 1.
  unfold R.v42766, N.v42766.
  rewrite ?node_42764.
  rewrite ?node_42765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42767 (s : N.State) (i : N.Inputs) :
  R.v42767 (state s) (inputs i) = Zmod.unsigned (N.v42767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42767 s i)) at 1.
  unfold R.v42767, N.v42767.
  unfold R.v16484, N.v16484.
  rewrite ?node_42766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42768 (s : N.State) (i : N.Inputs) :
  R.v42768 (state s) (inputs i) = Zmod.unsigned (N.v42768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42768 s i)) at 1.
  unfold R.v42768, N.v42768.
  rewrite ?node_42761.
  rewrite ?node_42762.
  rewrite ?node_42763.
  rewrite ?node_42767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42769 (s : N.State) (i : N.Inputs) :
  R.v42769 (state s) (inputs i) = Zmod.unsigned (N.v42769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42769 s i)) at 1.
  unfold R.v42769, N.v42769.
  unfold R.v6, N.v6.
  rewrite ?node_42768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42770 (s : N.State) (i : N.Inputs) :
  R.v42770 (state s) (inputs i) = Zmod.unsigned (N.v42770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42770 s i)) at 1.
  unfold R.v42770, N.v42770.
  rewrite ?node_10230.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42771 (s : N.State) (i : N.Inputs) :
  R.v42771 (state s) (inputs i) = Zmod.unsigned (N.v42771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42771 s i)) at 1.
  unfold R.v42771, N.v42771.
  unfold R.v6, N.v6.
  rewrite ?node_10387.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42772 (s : N.State) (i : N.Inputs) :
  R.v42772 (state s) (inputs i) = Zmod.unsigned (N.v42772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42772 s i)) at 1.
  unfold R.v42772, N.v42772.
  unfold R.v6, N.v6.
  rewrite ?node_10416.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42773 (s : N.State) (i : N.Inputs) :
  R.v42773 (state s) (inputs i) = Zmod.unsigned (N.v42773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42773 s i)) at 1.
  unfold R.v42773, N.v42773.
  rewrite ?node_42770.
  rewrite ?node_42771.
  rewrite ?node_42772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42774 (s : N.State) (i : N.Inputs) :
  R.v42774 (state s) (inputs i) = Zmod.unsigned (N.v42774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42774 s i)) at 1.
  unfold R.v42774, N.v42774.
  rewrite ?node_42769.
  rewrite ?node_42773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42775 (s : N.State) (i : N.Inputs) :
  R.v42775 (state s) (inputs i) = Zmod.unsigned (N.v42775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42775 s i)) at 1.
  unfold R.v42775, N.v42775.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42776 (s : N.State) (i : N.Inputs) :
  R.v42776 (state s) (inputs i) = Zmod.unsigned (N.v42776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42776 s i)) at 1.
  unfold R.v42776, N.v42776.
  rewrite ?node_10221.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42777 (s : N.State) (i : N.Inputs) :
  R.v42777 (state s) (inputs i) = Zmod.unsigned (N.v42777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42777 s i)) at 1.
  unfold R.v42777, N.v42777.
  unfold R.v6, N.v6.
  rewrite ?node_10217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42778 (s : N.State) (i : N.Inputs) :
  R.v42778 (state s) (inputs i) = Zmod.unsigned (N.v42778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42778 s i)) at 1.
  unfold R.v42778, N.v42778.
  unfold R.v6, N.v6.
  rewrite ?node_10214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42779 (s : N.State) (i : N.Inputs) :
  R.v42779 (state s) (inputs i) = Zmod.unsigned (N.v42779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42779 s i)) at 1.
  unfold R.v42779, N.v42779.
  rewrite ?node_42777.
  rewrite ?node_42778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42780 (s : N.State) (i : N.Inputs) :
  R.v42780 (state s) (inputs i) = Zmod.unsigned (N.v42780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42780 s i)) at 1.
  unfold R.v42780, N.v42780.
  unfold R.v16484, N.v16484.
  rewrite ?node_42779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42781 (s : N.State) (i : N.Inputs) :
  R.v42781 (state s) (inputs i) = Zmod.unsigned (N.v42781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42781 s i)) at 1.
  unfold R.v42781, N.v42781.
  rewrite ?node_42776.
  rewrite ?node_42780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42782 (s : N.State) (i : N.Inputs) :
  R.v42782 (state s) (inputs i) = Zmod.unsigned (N.v42782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42782 s i)) at 1.
  unfold R.v42782, N.v42782.
  unfold R.v6, N.v6.
  rewrite ?node_42781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42783 (s : N.State) (i : N.Inputs) :
  R.v42783 (state s) (inputs i) = Zmod.unsigned (N.v42783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42783 s i)) at 1.
  unfold R.v42783, N.v42783.
  rewrite ?node_10222.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42784 (s : N.State) (i : N.Inputs) :
  R.v42784 (state s) (inputs i) = Zmod.unsigned (N.v42784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42784 s i)) at 1.
  unfold R.v42784, N.v42784.
  unfold R.v6, N.v6.
  rewrite ?node_10387.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42785 (s : N.State) (i : N.Inputs) :
  R.v42785 (state s) (inputs i) = Zmod.unsigned (N.v42785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42785 s i)) at 1.
  unfold R.v42785, N.v42785.
  rewrite ?node_42783.
  rewrite ?node_42784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42786 (s : N.State) (i : N.Inputs) :
  R.v42786 (state s) (inputs i) = Zmod.unsigned (N.v42786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42786 s i)) at 1.
  unfold R.v42786, N.v42786.
  rewrite ?node_42782.
  rewrite ?node_42785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42787 (s : N.State) (i : N.Inputs) :
  R.v42787 (state s) (inputs i) = Zmod.unsigned (N.v42787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42787 s i)) at 1.
  unfold R.v42787, N.v42787.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42788 (s : N.State) (i : N.Inputs) :
  R.v42788 (state s) (inputs i) = Zmod.unsigned (N.v42788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42788 s i)) at 1.
  unfold R.v42788, N.v42788.
  rewrite ?node_10229.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42789 (s : N.State) (i : N.Inputs) :
  R.v42789 (state s) (inputs i) = Zmod.unsigned (N.v42789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42789 s i)) at 1.
  unfold R.v42789, N.v42789.
  unfold R.v6, N.v6.
  rewrite ?node_10225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42790 (s : N.State) (i : N.Inputs) :
  R.v42790 (state s) (inputs i) = Zmod.unsigned (N.v42790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42790 s i)) at 1.
  unfold R.v42790, N.v42790.
  unfold R.v6, N.v6.
  rewrite ?node_10222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42791 (s : N.State) (i : N.Inputs) :
  R.v42791 (state s) (inputs i) = Zmod.unsigned (N.v42791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42791 s i)) at 1.
  unfold R.v42791, N.v42791.
  rewrite ?node_42789.
  rewrite ?node_42790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42792 (s : N.State) (i : N.Inputs) :
  R.v42792 (state s) (inputs i) = Zmod.unsigned (N.v42792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42792 s i)) at 1.
  unfold R.v42792, N.v42792.
  unfold R.v16484, N.v16484.
  rewrite ?node_42791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42793 (s : N.State) (i : N.Inputs) :
  R.v42793 (state s) (inputs i) = Zmod.unsigned (N.v42793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42793 s i)) at 1.
  unfold R.v42793, N.v42793.
  rewrite ?node_42788.
  rewrite ?node_42792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42794 (s : N.State) (i : N.Inputs) :
  R.v42794 (state s) (inputs i) = Zmod.unsigned (N.v42794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42794 s i)) at 1.
  unfold R.v42794, N.v42794.
  unfold R.v6, N.v6.
  rewrite ?node_42793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42795 (s : N.State) (i : N.Inputs) :
  R.v42795 (state s) (inputs i) = Zmod.unsigned (N.v42795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42795 s i)) at 1.
  unfold R.v42795, N.v42795.
  rewrite ?node_10230.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42796 (s : N.State) (i : N.Inputs) :
  R.v42796 (state s) (inputs i) = Zmod.unsigned (N.v42796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42796 s i)) at 1.
  unfold R.v42796, N.v42796.
  unfold R.v6, N.v6.
  rewrite ?node_10416.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42797 (s : N.State) (i : N.Inputs) :
  R.v42797 (state s) (inputs i) = Zmod.unsigned (N.v42797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42797 s i)) at 1.
  unfold R.v42797, N.v42797.
  rewrite ?node_42795.
  rewrite ?node_42796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42798 (s : N.State) (i : N.Inputs) :
  R.v42798 (state s) (inputs i) = Zmod.unsigned (N.v42798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42798 s i)) at 1.
  unfold R.v42798, N.v42798.
  rewrite ?node_42794.
  rewrite ?node_42797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42799 (s : N.State) (i : N.Inputs) :
  R.v42799 (state s) (inputs i) = Zmod.unsigned (N.v42799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42799 s i)) at 1.
  unfold R.v42799, N.v42799.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42800 (s : N.State) (i : N.Inputs) :
  R.v42800 (state s) (inputs i) = Zmod.unsigned (N.v42800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42800 s i)) at 1.
  unfold R.v42800, N.v42800.
  rewrite ?node_10314.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42801 (s : N.State) (i : N.Inputs) :
  R.v42801 (state s) (inputs i) = Zmod.unsigned (N.v42801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42801 s i)) at 1.
  unfold R.v42801, N.v42801.
  rewrite ?node_10310.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42802 (s : N.State) (i : N.Inputs) :
  R.v42802 (state s) (inputs i) = Zmod.unsigned (N.v42802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42802 s i)) at 1.
  unfold R.v42802, N.v42802.
  rewrite ?node_10302.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42803 (s : N.State) (i : N.Inputs) :
  R.v42803 (state s) (inputs i) = Zmod.unsigned (N.v42803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42803 s i)) at 1.
  unfold R.v42803, N.v42803.
  unfold R.v6, N.v6.
  rewrite ?node_10294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42804 (s : N.State) (i : N.Inputs) :
  R.v42804 (state s) (inputs i) = Zmod.unsigned (N.v42804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42804 s i)) at 1.
  unfold R.v42804, N.v42804.
  unfold R.v6, N.v6.
  rewrite ?node_10287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42805 (s : N.State) (i : N.Inputs) :
  R.v42805 (state s) (inputs i) = Zmod.unsigned (N.v42805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42805 s i)) at 1.
  unfold R.v42805, N.v42805.
  rewrite ?node_42803.
  rewrite ?node_42804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42806 (s : N.State) (i : N.Inputs) :
  R.v42806 (state s) (inputs i) = Zmod.unsigned (N.v42806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42806 s i)) at 1.
  unfold R.v42806, N.v42806.
  unfold R.v16484, N.v16484.
  rewrite ?node_42805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42807 (s : N.State) (i : N.Inputs) :
  R.v42807 (state s) (inputs i) = Zmod.unsigned (N.v42807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42807 s i)) at 1.
  unfold R.v42807, N.v42807.
  rewrite ?node_42800.
  rewrite ?node_42801.
  rewrite ?node_42802.
  rewrite ?node_42806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42808 (s : N.State) (i : N.Inputs) :
  R.v42808 (state s) (inputs i) = Zmod.unsigned (N.v42808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42808 s i)) at 1.
  unfold R.v42808, N.v42808.
  unfold R.v6, N.v6.
  rewrite ?node_42807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42809 (s : N.State) (i : N.Inputs) :
  R.v42809 (state s) (inputs i) = Zmod.unsigned (N.v42809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42809 s i)) at 1.
  unfold R.v42809, N.v42809.
  rewrite ?node_10315.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42810 (s : N.State) (i : N.Inputs) :
  R.v42810 (state s) (inputs i) = Zmod.unsigned (N.v42810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42810 s i)) at 1.
  unfold R.v42810, N.v42810.
  unfold R.v6, N.v6.
  rewrite ?node_10472.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42811 (s : N.State) (i : N.Inputs) :
  R.v42811 (state s) (inputs i) = Zmod.unsigned (N.v42811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42811 s i)) at 1.
  unfold R.v42811, N.v42811.
  unfold R.v6, N.v6.
  rewrite ?node_10559.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42812 (s : N.State) (i : N.Inputs) :
  R.v42812 (state s) (inputs i) = Zmod.unsigned (N.v42812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42812 s i)) at 1.
  unfold R.v42812, N.v42812.
  rewrite ?node_42809.
  rewrite ?node_42810.
  rewrite ?node_42811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42813 (s : N.State) (i : N.Inputs) :
  R.v42813 (state s) (inputs i) = Zmod.unsigned (N.v42813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42813 s i)) at 1.
  unfold R.v42813, N.v42813.
  rewrite ?node_42808.
  rewrite ?node_42812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42814 (s : N.State) (i : N.Inputs) :
  R.v42814 (state s) (inputs i) = Zmod.unsigned (N.v42814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42814 s i)) at 1.
  unfold R.v42814, N.v42814.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42815 (s : N.State) (i : N.Inputs) :
  R.v42815 (state s) (inputs i) = Zmod.unsigned (N.v42815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42815 s i)) at 1.
  unfold R.v42815, N.v42815.
  rewrite ?node_10302.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42816 (s : N.State) (i : N.Inputs) :
  R.v42816 (state s) (inputs i) = Zmod.unsigned (N.v42816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42816 s i)) at 1.
  unfold R.v42816, N.v42816.
  unfold R.v6, N.v6.
  rewrite ?node_10294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42817 (s : N.State) (i : N.Inputs) :
  R.v42817 (state s) (inputs i) = Zmod.unsigned (N.v42817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42817 s i)) at 1.
  unfold R.v42817, N.v42817.
  unfold R.v6, N.v6.
  rewrite ?node_10287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42818 (s : N.State) (i : N.Inputs) :
  R.v42818 (state s) (inputs i) = Zmod.unsigned (N.v42818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42818 s i)) at 1.
  unfold R.v42818, N.v42818.
  rewrite ?node_42816.
  rewrite ?node_42817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42819 (s : N.State) (i : N.Inputs) :
  R.v42819 (state s) (inputs i) = Zmod.unsigned (N.v42819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42819 s i)) at 1.
  unfold R.v42819, N.v42819.
  unfold R.v16484, N.v16484.
  rewrite ?node_42818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42820 (s : N.State) (i : N.Inputs) :
  R.v42820 (state s) (inputs i) = Zmod.unsigned (N.v42820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42820 s i)) at 1.
  unfold R.v42820, N.v42820.
  rewrite ?node_42815.
  rewrite ?node_42819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42821 (s : N.State) (i : N.Inputs) :
  R.v42821 (state s) (inputs i) = Zmod.unsigned (N.v42821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42821 s i)) at 1.
  unfold R.v42821, N.v42821.
  unfold R.v6, N.v6.
  rewrite ?node_42820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42822 (s : N.State) (i : N.Inputs) :
  R.v42822 (state s) (inputs i) = Zmod.unsigned (N.v42822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42822 s i)) at 1.
  unfold R.v42822, N.v42822.
  rewrite ?node_10303.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42823 (s : N.State) (i : N.Inputs) :
  R.v42823 (state s) (inputs i) = Zmod.unsigned (N.v42823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42823 s i)) at 1.
  unfold R.v42823, N.v42823.
  unfold R.v6, N.v6.
  rewrite ?node_10472.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42824 (s : N.State) (i : N.Inputs) :
  R.v42824 (state s) (inputs i) = Zmod.unsigned (N.v42824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42824 s i)) at 1.
  unfold R.v42824, N.v42824.
  rewrite ?node_42822.
  rewrite ?node_42823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42825 (s : N.State) (i : N.Inputs) :
  R.v42825 (state s) (inputs i) = Zmod.unsigned (N.v42825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42825 s i)) at 1.
  unfold R.v42825, N.v42825.
  rewrite ?node_42821.
  rewrite ?node_42824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42826 (s : N.State) (i : N.Inputs) :
  R.v42826 (state s) (inputs i) = Zmod.unsigned (N.v42826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42826 s i)) at 1.
  unfold R.v42826, N.v42826.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42827 (s : N.State) (i : N.Inputs) :
  R.v42827 (state s) (inputs i) = Zmod.unsigned (N.v42827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42827 s i)) at 1.
  unfold R.v42827, N.v42827.
  rewrite ?node_10314.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42828 (s : N.State) (i : N.Inputs) :
  R.v42828 (state s) (inputs i) = Zmod.unsigned (N.v42828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42828 s i)) at 1.
  unfold R.v42828, N.v42828.
  unfold R.v6, N.v6.
  rewrite ?node_10310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42829 (s : N.State) (i : N.Inputs) :
  R.v42829 (state s) (inputs i) = Zmod.unsigned (N.v42829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42829 s i)) at 1.
  unfold R.v42829, N.v42829.
  unfold R.v6, N.v6.
  rewrite ?node_10303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42830 (s : N.State) (i : N.Inputs) :
  R.v42830 (state s) (inputs i) = Zmod.unsigned (N.v42830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42830 s i)) at 1.
  unfold R.v42830, N.v42830.
  rewrite ?node_42828.
  rewrite ?node_42829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42831 (s : N.State) (i : N.Inputs) :
  R.v42831 (state s) (inputs i) = Zmod.unsigned (N.v42831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42831 s i)) at 1.
  unfold R.v42831, N.v42831.
  unfold R.v16484, N.v16484.
  rewrite ?node_42830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42832 (s : N.State) (i : N.Inputs) :
  R.v42832 (state s) (inputs i) = Zmod.unsigned (N.v42832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42832 s i)) at 1.
  unfold R.v42832, N.v42832.
  rewrite ?node_42827.
  rewrite ?node_42831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42833 (s : N.State) (i : N.Inputs) :
  R.v42833 (state s) (inputs i) = Zmod.unsigned (N.v42833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42833 s i)) at 1.
  unfold R.v42833, N.v42833.
  unfold R.v6, N.v6.
  rewrite ?node_42832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42834 (s : N.State) (i : N.Inputs) :
  R.v42834 (state s) (inputs i) = Zmod.unsigned (N.v42834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42834 s i)) at 1.
  unfold R.v42834, N.v42834.
  rewrite ?node_10315.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42835 (s : N.State) (i : N.Inputs) :
  R.v42835 (state s) (inputs i) = Zmod.unsigned (N.v42835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42835 s i)) at 1.
  unfold R.v42835, N.v42835.
  unfold R.v6, N.v6.
  rewrite ?node_10559.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42836 (s : N.State) (i : N.Inputs) :
  R.v42836 (state s) (inputs i) = Zmod.unsigned (N.v42836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42836 s i)) at 1.
  unfold R.v42836, N.v42836.
  rewrite ?node_42834.
  rewrite ?node_42835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42837 (s : N.State) (i : N.Inputs) :
  R.v42837 (state s) (inputs i) = Zmod.unsigned (N.v42837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42837 s i)) at 1.
  unfold R.v42837, N.v42837.
  rewrite ?node_42833.
  rewrite ?node_42836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42838 (s : N.State) (i : N.Inputs) :
  R.v42838 (state s) (inputs i) = Zmod.unsigned (N.v42838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42838 s i)) at 1.
  unfold R.v42838, N.v42838.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42839 (s : N.State) (i : N.Inputs) :
  R.v42839 (state s) (inputs i) = Zmod.unsigned (N.v42839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42839 s i)) at 1.
  unfold R.v42839, N.v42839.
  rewrite ?node_10349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42840 (s : N.State) (i : N.Inputs) :
  R.v42840 (state s) (inputs i) = Zmod.unsigned (N.v42840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42840 s i)) at 1.
  unfold R.v42840, N.v42840.
  rewrite ?node_10345.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42841 (s : N.State) (i : N.Inputs) :
  R.v42841 (state s) (inputs i) = Zmod.unsigned (N.v42841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42841 s i)) at 1.
  unfold R.v42841, N.v42841.
  rewrite ?node_10337.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42842 (s : N.State) (i : N.Inputs) :
  R.v42842 (state s) (inputs i) = Zmod.unsigned (N.v42842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42842 s i)) at 1.
  unfold R.v42842, N.v42842.
  unfold R.v6, N.v6.
  rewrite ?node_10329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42843 (s : N.State) (i : N.Inputs) :
  R.v42843 (state s) (inputs i) = Zmod.unsigned (N.v42843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42843 s i)) at 1.
  unfold R.v42843, N.v42843.
  unfold R.v6, N.v6.
  rewrite ?node_10322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42844 (s : N.State) (i : N.Inputs) :
  R.v42844 (state s) (inputs i) = Zmod.unsigned (N.v42844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42844 s i)) at 1.
  unfold R.v42844, N.v42844.
  rewrite ?node_42842.
  rewrite ?node_42843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42845 (s : N.State) (i : N.Inputs) :
  R.v42845 (state s) (inputs i) = Zmod.unsigned (N.v42845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42845 s i)) at 1.
  unfold R.v42845, N.v42845.
  unfold R.v16484, N.v16484.
  rewrite ?node_42844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42846 (s : N.State) (i : N.Inputs) :
  R.v42846 (state s) (inputs i) = Zmod.unsigned (N.v42846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42846 s i)) at 1.
  unfold R.v42846, N.v42846.
  rewrite ?node_42839.
  rewrite ?node_42840.
  rewrite ?node_42841.
  rewrite ?node_42845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42847 (s : N.State) (i : N.Inputs) :
  R.v42847 (state s) (inputs i) = Zmod.unsigned (N.v42847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42847 s i)) at 1.
  unfold R.v42847, N.v42847.
  unfold R.v6, N.v6.
  rewrite ?node_42846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42848 (s : N.State) (i : N.Inputs) :
  R.v42848 (state s) (inputs i) = Zmod.unsigned (N.v42848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42848 s i)) at 1.
  unfold R.v42848, N.v42848.
  rewrite ?node_10350.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42849 (s : N.State) (i : N.Inputs) :
  R.v42849 (state s) (inputs i) = Zmod.unsigned (N.v42849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42849 s i)) at 1.
  unfold R.v42849, N.v42849.
  unfold R.v6, N.v6.
  rewrite ?node_10507.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42850 (s : N.State) (i : N.Inputs) :
  R.v42850 (state s) (inputs i) = Zmod.unsigned (N.v42850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42850 s i)) at 1.
  unfold R.v42850, N.v42850.
  unfold R.v6, N.v6.
  rewrite ?node_10563.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42851 (s : N.State) (i : N.Inputs) :
  R.v42851 (state s) (inputs i) = Zmod.unsigned (N.v42851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42851 s i)) at 1.
  unfold R.v42851, N.v42851.
  rewrite ?node_42848.
  rewrite ?node_42849.
  rewrite ?node_42850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42852 (s : N.State) (i : N.Inputs) :
  R.v42852 (state s) (inputs i) = Zmod.unsigned (N.v42852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42852 s i)) at 1.
  unfold R.v42852, N.v42852.
  rewrite ?node_42847.
  rewrite ?node_42851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42853 (s : N.State) (i : N.Inputs) :
  R.v42853 (state s) (inputs i) = Zmod.unsigned (N.v42853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42853 s i)) at 1.
  unfold R.v42853, N.v42853.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42854 (s : N.State) (i : N.Inputs) :
  R.v42854 (state s) (inputs i) = Zmod.unsigned (N.v42854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42854 s i)) at 1.
  unfold R.v42854, N.v42854.
  rewrite ?node_10337.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42855 (s : N.State) (i : N.Inputs) :
  R.v42855 (state s) (inputs i) = Zmod.unsigned (N.v42855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42855 s i)) at 1.
  unfold R.v42855, N.v42855.
  unfold R.v6, N.v6.
  rewrite ?node_10329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42856 (s : N.State) (i : N.Inputs) :
  R.v42856 (state s) (inputs i) = Zmod.unsigned (N.v42856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42856 s i)) at 1.
  unfold R.v42856, N.v42856.
  unfold R.v6, N.v6.
  rewrite ?node_10322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42857 (s : N.State) (i : N.Inputs) :
  R.v42857 (state s) (inputs i) = Zmod.unsigned (N.v42857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42857 s i)) at 1.
  unfold R.v42857, N.v42857.
  rewrite ?node_42855.
  rewrite ?node_42856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42858 (s : N.State) (i : N.Inputs) :
  R.v42858 (state s) (inputs i) = Zmod.unsigned (N.v42858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42858 s i)) at 1.
  unfold R.v42858, N.v42858.
  unfold R.v16484, N.v16484.
  rewrite ?node_42857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42859 (s : N.State) (i : N.Inputs) :
  R.v42859 (state s) (inputs i) = Zmod.unsigned (N.v42859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42859 s i)) at 1.
  unfold R.v42859, N.v42859.
  rewrite ?node_42854.
  rewrite ?node_42858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42860 (s : N.State) (i : N.Inputs) :
  R.v42860 (state s) (inputs i) = Zmod.unsigned (N.v42860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42860 s i)) at 1.
  unfold R.v42860, N.v42860.
  unfold R.v6, N.v6.
  rewrite ?node_42859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42861 (s : N.State) (i : N.Inputs) :
  R.v42861 (state s) (inputs i) = Zmod.unsigned (N.v42861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42861 s i)) at 1.
  unfold R.v42861, N.v42861.
  rewrite ?node_10338.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42862 (s : N.State) (i : N.Inputs) :
  R.v42862 (state s) (inputs i) = Zmod.unsigned (N.v42862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42862 s i)) at 1.
  unfold R.v42862, N.v42862.
  unfold R.v6, N.v6.
  rewrite ?node_10507.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42863 (s : N.State) (i : N.Inputs) :
  R.v42863 (state s) (inputs i) = Zmod.unsigned (N.v42863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42863 s i)) at 1.
  unfold R.v42863, N.v42863.
  rewrite ?node_42861.
  rewrite ?node_42862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42864 (s : N.State) (i : N.Inputs) :
  R.v42864 (state s) (inputs i) = Zmod.unsigned (N.v42864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42864 s i)) at 1.
  unfold R.v42864, N.v42864.
  rewrite ?node_42860.
  rewrite ?node_42863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42865 (s : N.State) (i : N.Inputs) :
  R.v42865 (state s) (inputs i) = Zmod.unsigned (N.v42865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42865 s i)) at 1.
  unfold R.v42865, N.v42865.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42866 (s : N.State) (i : N.Inputs) :
  R.v42866 (state s) (inputs i) = Zmod.unsigned (N.v42866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42866 s i)) at 1.
  unfold R.v42866, N.v42866.
  rewrite ?node_10349.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42867 (s : N.State) (i : N.Inputs) :
  R.v42867 (state s) (inputs i) = Zmod.unsigned (N.v42867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42867 s i)) at 1.
  unfold R.v42867, N.v42867.
  unfold R.v6, N.v6.
  rewrite ?node_10345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42868 (s : N.State) (i : N.Inputs) :
  R.v42868 (state s) (inputs i) = Zmod.unsigned (N.v42868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42868 s i)) at 1.
  unfold R.v42868, N.v42868.
  unfold R.v6, N.v6.
  rewrite ?node_10338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42869 (s : N.State) (i : N.Inputs) :
  R.v42869 (state s) (inputs i) = Zmod.unsigned (N.v42869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42869 s i)) at 1.
  unfold R.v42869, N.v42869.
  rewrite ?node_42867.
  rewrite ?node_42868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42870 (s : N.State) (i : N.Inputs) :
  R.v42870 (state s) (inputs i) = Zmod.unsigned (N.v42870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42870 s i)) at 1.
  unfold R.v42870, N.v42870.
  unfold R.v16484, N.v16484.
  rewrite ?node_42869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42871 (s : N.State) (i : N.Inputs) :
  R.v42871 (state s) (inputs i) = Zmod.unsigned (N.v42871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42871 s i)) at 1.
  unfold R.v42871, N.v42871.
  rewrite ?node_42866.
  rewrite ?node_42870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42872 (s : N.State) (i : N.Inputs) :
  R.v42872 (state s) (inputs i) = Zmod.unsigned (N.v42872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42872 s i)) at 1.
  unfold R.v42872, N.v42872.
  unfold R.v6, N.v6.
  rewrite ?node_42871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42873 (s : N.State) (i : N.Inputs) :
  R.v42873 (state s) (inputs i) = Zmod.unsigned (N.v42873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42873 s i)) at 1.
  unfold R.v42873, N.v42873.
  rewrite ?node_10350.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42874 (s : N.State) (i : N.Inputs) :
  R.v42874 (state s) (inputs i) = Zmod.unsigned (N.v42874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42874 s i)) at 1.
  unfold R.v42874, N.v42874.
  unfold R.v6, N.v6.
  rewrite ?node_10563.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42875 (s : N.State) (i : N.Inputs) :
  R.v42875 (state s) (inputs i) = Zmod.unsigned (N.v42875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42875 s i)) at 1.
  unfold R.v42875, N.v42875.
  rewrite ?node_42873.
  rewrite ?node_42874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42876 (s : N.State) (i : N.Inputs) :
  R.v42876 (state s) (inputs i) = Zmod.unsigned (N.v42876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42876 s i)) at 1.
  unfold R.v42876, N.v42876.
  rewrite ?node_42872.
  rewrite ?node_42875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42877 (s : N.State) (i : N.Inputs) :
  R.v42877 (state s) (inputs i) = Zmod.unsigned (N.v42877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42877 s i)) at 1.
  unfold R.v42877, N.v42877.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42878 (s : N.State) (i : N.Inputs) :
  R.v42878 (state s) (inputs i) = Zmod.unsigned (N.v42878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42878 s i)) at 1.
  unfold R.v42878, N.v42878.
  rewrite ?node_10367.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42879 (s : N.State) (i : N.Inputs) :
  R.v42879 (state s) (inputs i) = Zmod.unsigned (N.v42879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42879 s i)) at 1.
  unfold R.v42879, N.v42879.
  rewrite ?node_10363.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42880 (s : N.State) (i : N.Inputs) :
  R.v42880 (state s) (inputs i) = Zmod.unsigned (N.v42880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42880 s i)) at 1.
  unfold R.v42880, N.v42880.
  rewrite ?node_10359.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42881 (s : N.State) (i : N.Inputs) :
  R.v42881 (state s) (inputs i) = Zmod.unsigned (N.v42881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42881 s i)) at 1.
  unfold R.v42881, N.v42881.
  unfold R.v6, N.v6.
  rewrite ?node_10355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42882 (s : N.State) (i : N.Inputs) :
  R.v42882 (state s) (inputs i) = Zmod.unsigned (N.v42882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42882 s i)) at 1.
  unfold R.v42882, N.v42882.
  unfold R.v6, N.v6.
  rewrite ?node_10352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42883 (s : N.State) (i : N.Inputs) :
  R.v42883 (state s) (inputs i) = Zmod.unsigned (N.v42883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42883 s i)) at 1.
  unfold R.v42883, N.v42883.
  rewrite ?node_42881.
  rewrite ?node_42882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42884 (s : N.State) (i : N.Inputs) :
  R.v42884 (state s) (inputs i) = Zmod.unsigned (N.v42884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42884 s i)) at 1.
  unfold R.v42884, N.v42884.
  unfold R.v16484, N.v16484.
  rewrite ?node_42883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42885 (s : N.State) (i : N.Inputs) :
  R.v42885 (state s) (inputs i) = Zmod.unsigned (N.v42885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42885 s i)) at 1.
  unfold R.v42885, N.v42885.
  rewrite ?node_42878.
  rewrite ?node_42879.
  rewrite ?node_42880.
  rewrite ?node_42884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42886 (s : N.State) (i : N.Inputs) :
  R.v42886 (state s) (inputs i) = Zmod.unsigned (N.v42886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42886 s i)) at 1.
  unfold R.v42886, N.v42886.
  unfold R.v6, N.v6.
  rewrite ?node_42885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42887 (s : N.State) (i : N.Inputs) :
  R.v42887 (state s) (inputs i) = Zmod.unsigned (N.v42887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42887 s i)) at 1.
  unfold R.v42887, N.v42887.
  rewrite ?node_10368.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42888 (s : N.State) (i : N.Inputs) :
  R.v42888 (state s) (inputs i) = Zmod.unsigned (N.v42888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42888 s i)) at 1.
  unfold R.v42888, N.v42888.
  unfold R.v6, N.v6.
  rewrite ?node_10525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42889 (s : N.State) (i : N.Inputs) :
  R.v42889 (state s) (inputs i) = Zmod.unsigned (N.v42889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42889 s i)) at 1.
  unfold R.v42889, N.v42889.
  unfold R.v6, N.v6.
  rewrite ?node_10567.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42890 (s : N.State) (i : N.Inputs) :
  R.v42890 (state s) (inputs i) = Zmod.unsigned (N.v42890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42890 s i)) at 1.
  unfold R.v42890, N.v42890.
  rewrite ?node_42887.
  rewrite ?node_42888.
  rewrite ?node_42889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42891 (s : N.State) (i : N.Inputs) :
  R.v42891 (state s) (inputs i) = Zmod.unsigned (N.v42891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42891 s i)) at 1.
  unfold R.v42891, N.v42891.
  rewrite ?node_42886.
  rewrite ?node_42890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42892 (s : N.State) (i : N.Inputs) :
  R.v42892 (state s) (inputs i) = Zmod.unsigned (N.v42892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42892 s i)) at 1.
  unfold R.v42892, N.v42892.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42893 (s : N.State) (i : N.Inputs) :
  R.v42893 (state s) (inputs i) = Zmod.unsigned (N.v42893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42893 s i)) at 1.
  unfold R.v42893, N.v42893.
  rewrite ?node_10359.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42894 (s : N.State) (i : N.Inputs) :
  R.v42894 (state s) (inputs i) = Zmod.unsigned (N.v42894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42894 s i)) at 1.
  unfold R.v42894, N.v42894.
  unfold R.v6, N.v6.
  rewrite ?node_10355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42895 (s : N.State) (i : N.Inputs) :
  R.v42895 (state s) (inputs i) = Zmod.unsigned (N.v42895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42895 s i)) at 1.
  unfold R.v42895, N.v42895.
  unfold R.v6, N.v6.
  rewrite ?node_10352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42896 (s : N.State) (i : N.Inputs) :
  R.v42896 (state s) (inputs i) = Zmod.unsigned (N.v42896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42896 s i)) at 1.
  unfold R.v42896, N.v42896.
  rewrite ?node_42894.
  rewrite ?node_42895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42897 (s : N.State) (i : N.Inputs) :
  R.v42897 (state s) (inputs i) = Zmod.unsigned (N.v42897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42897 s i)) at 1.
  unfold R.v42897, N.v42897.
  unfold R.v16484, N.v16484.
  rewrite ?node_42896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42898 (s : N.State) (i : N.Inputs) :
  R.v42898 (state s) (inputs i) = Zmod.unsigned (N.v42898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42898 s i)) at 1.
  unfold R.v42898, N.v42898.
  rewrite ?node_42893.
  rewrite ?node_42897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42899 (s : N.State) (i : N.Inputs) :
  R.v42899 (state s) (inputs i) = Zmod.unsigned (N.v42899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42899 s i)) at 1.
  unfold R.v42899, N.v42899.
  unfold R.v6, N.v6.
  rewrite ?node_42898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42900 (s : N.State) (i : N.Inputs) :
  R.v42900 (state s) (inputs i) = Zmod.unsigned (N.v42900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42900 s i)) at 1.
  unfold R.v42900, N.v42900.
  rewrite ?node_10360.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42901 (s : N.State) (i : N.Inputs) :
  R.v42901 (state s) (inputs i) = Zmod.unsigned (N.v42901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42901 s i)) at 1.
  unfold R.v42901, N.v42901.
  unfold R.v6, N.v6.
  rewrite ?node_10525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42902 (s : N.State) (i : N.Inputs) :
  R.v42902 (state s) (inputs i) = Zmod.unsigned (N.v42902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42902 s i)) at 1.
  unfold R.v42902, N.v42902.
  rewrite ?node_42900.
  rewrite ?node_42901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42903 (s : N.State) (i : N.Inputs) :
  R.v42903 (state s) (inputs i) = Zmod.unsigned (N.v42903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42903 s i)) at 1.
  unfold R.v42903, N.v42903.
  rewrite ?node_42899.
  rewrite ?node_42902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42904 (s : N.State) (i : N.Inputs) :
  R.v42904 (state s) (inputs i) = Zmod.unsigned (N.v42904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42904 s i)) at 1.
  unfold R.v42904, N.v42904.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42905 (s : N.State) (i : N.Inputs) :
  R.v42905 (state s) (inputs i) = Zmod.unsigned (N.v42905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42905 s i)) at 1.
  unfold R.v42905, N.v42905.
  rewrite ?node_10367.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42906 (s : N.State) (i : N.Inputs) :
  R.v42906 (state s) (inputs i) = Zmod.unsigned (N.v42906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42906 s i)) at 1.
  unfold R.v42906, N.v42906.
  unfold R.v6, N.v6.
  rewrite ?node_10363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42907 (s : N.State) (i : N.Inputs) :
  R.v42907 (state s) (inputs i) = Zmod.unsigned (N.v42907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42907 s i)) at 1.
  unfold R.v42907, N.v42907.
  unfold R.v6, N.v6.
  rewrite ?node_10360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42908 (s : N.State) (i : N.Inputs) :
  R.v42908 (state s) (inputs i) = Zmod.unsigned (N.v42908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42908 s i)) at 1.
  unfold R.v42908, N.v42908.
  rewrite ?node_42906.
  rewrite ?node_42907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42909 (s : N.State) (i : N.Inputs) :
  R.v42909 (state s) (inputs i) = Zmod.unsigned (N.v42909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42909 s i)) at 1.
  unfold R.v42909, N.v42909.
  unfold R.v16484, N.v16484.
  rewrite ?node_42908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42910 (s : N.State) (i : N.Inputs) :
  R.v42910 (state s) (inputs i) = Zmod.unsigned (N.v42910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42910 s i)) at 1.
  unfold R.v42910, N.v42910.
  rewrite ?node_42905.
  rewrite ?node_42909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42911 (s : N.State) (i : N.Inputs) :
  R.v42911 (state s) (inputs i) = Zmod.unsigned (N.v42911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42911 s i)) at 1.
  unfold R.v42911, N.v42911.
  unfold R.v6, N.v6.
  rewrite ?node_42910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42912 (s : N.State) (i : N.Inputs) :
  R.v42912 (state s) (inputs i) = Zmod.unsigned (N.v42912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42912 s i)) at 1.
  unfold R.v42912, N.v42912.
  rewrite ?node_10368.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42913 (s : N.State) (i : N.Inputs) :
  R.v42913 (state s) (inputs i) = Zmod.unsigned (N.v42913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42913 s i)) at 1.
  unfold R.v42913, N.v42913.
  unfold R.v6, N.v6.
  rewrite ?node_10567.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42914 (s : N.State) (i : N.Inputs) :
  R.v42914 (state s) (inputs i) = Zmod.unsigned (N.v42914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42914 s i)) at 1.
  unfold R.v42914, N.v42914.
  rewrite ?node_42912.
  rewrite ?node_42913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42915 (s : N.State) (i : N.Inputs) :
  R.v42915 (state s) (inputs i) = Zmod.unsigned (N.v42915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42915 s i)) at 1.
  unfold R.v42915, N.v42915.
  rewrite ?node_42911.
  rewrite ?node_42914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42916 (s : N.State) (i : N.Inputs) :
  R.v42916 (state s) (inputs i) = Zmod.unsigned (N.v42916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42916 s i)) at 1.
  unfold R.v42916, N.v42916.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42917 (s : N.State) (i : N.Inputs) :
  R.v42917 (state s) (inputs i) = Zmod.unsigned (N.v42917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42917 s i)) at 1.
  unfold R.v42917, N.v42917.
  rewrite ?node_10387.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42918 (s : N.State) (i : N.Inputs) :
  R.v42918 (state s) (inputs i) = Zmod.unsigned (N.v42918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42918 s i)) at 1.
  unfold R.v42918, N.v42918.
  rewrite ?node_10383.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42919 (s : N.State) (i : N.Inputs) :
  R.v42919 (state s) (inputs i) = Zmod.unsigned (N.v42919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42919 s i)) at 1.
  unfold R.v42919, N.v42919.
  rewrite ?node_10379.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42920 (s : N.State) (i : N.Inputs) :
  R.v42920 (state s) (inputs i) = Zmod.unsigned (N.v42920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42920 s i)) at 1.
  unfold R.v42920, N.v42920.
  unfold R.v6, N.v6.
  rewrite ?node_10375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42921 (s : N.State) (i : N.Inputs) :
  R.v42921 (state s) (inputs i) = Zmod.unsigned (N.v42921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42921 s i)) at 1.
  unfold R.v42921, N.v42921.
  unfold R.v6, N.v6.
  rewrite ?node_10372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42922 (s : N.State) (i : N.Inputs) :
  R.v42922 (state s) (inputs i) = Zmod.unsigned (N.v42922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42922 s i)) at 1.
  unfold R.v42922, N.v42922.
  rewrite ?node_42920.
  rewrite ?node_42921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42923 (s : N.State) (i : N.Inputs) :
  R.v42923 (state s) (inputs i) = Zmod.unsigned (N.v42923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42923 s i)) at 1.
  unfold R.v42923, N.v42923.
  unfold R.v16484, N.v16484.
  rewrite ?node_42922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42924 (s : N.State) (i : N.Inputs) :
  R.v42924 (state s) (inputs i) = Zmod.unsigned (N.v42924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42924 s i)) at 1.
  unfold R.v42924, N.v42924.
  rewrite ?node_42917.
  rewrite ?node_42918.
  rewrite ?node_42919.
  rewrite ?node_42923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42925 (s : N.State) (i : N.Inputs) :
  R.v42925 (state s) (inputs i) = Zmod.unsigned (N.v42925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42925 s i)) at 1.
  unfold R.v42925, N.v42925.
  unfold R.v6, N.v6.
  rewrite ?node_42924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42926 (s : N.State) (i : N.Inputs) :
  R.v42926 (state s) (inputs i) = Zmod.unsigned (N.v42926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42926 s i)) at 1.
  unfold R.v42926, N.v42926.
  rewrite ?node_10388.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42927 (s : N.State) (i : N.Inputs) :
  R.v42927 (state s) (inputs i) = Zmod.unsigned (N.v42927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42927 s i)) at 1.
  unfold R.v42927, N.v42927.
  unfold R.v6, N.v6.
  rewrite ?node_10545.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42928 (s : N.State) (i : N.Inputs) :
  R.v42928 (state s) (inputs i) = Zmod.unsigned (N.v42928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42928 s i)) at 1.
  unfold R.v42928, N.v42928.
  unfold R.v6, N.v6.
  rewrite ?node_10576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42929 (s : N.State) (i : N.Inputs) :
  R.v42929 (state s) (inputs i) = Zmod.unsigned (N.v42929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42929 s i)) at 1.
  unfold R.v42929, N.v42929.
  rewrite ?node_42926.
  rewrite ?node_42927.
  rewrite ?node_42928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42930 (s : N.State) (i : N.Inputs) :
  R.v42930 (state s) (inputs i) = Zmod.unsigned (N.v42930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42930 s i)) at 1.
  unfold R.v42930, N.v42930.
  rewrite ?node_42925.
  rewrite ?node_42929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42931 (s : N.State) (i : N.Inputs) :
  R.v42931 (state s) (inputs i) = Zmod.unsigned (N.v42931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42931 s i)) at 1.
  unfold R.v42931, N.v42931.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42932 (s : N.State) (i : N.Inputs) :
  R.v42932 (state s) (inputs i) = Zmod.unsigned (N.v42932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42932 s i)) at 1.
  unfold R.v42932, N.v42932.
  rewrite ?node_10379.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42933 (s : N.State) (i : N.Inputs) :
  R.v42933 (state s) (inputs i) = Zmod.unsigned (N.v42933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42933 s i)) at 1.
  unfold R.v42933, N.v42933.
  unfold R.v6, N.v6.
  rewrite ?node_10375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42934 (s : N.State) (i : N.Inputs) :
  R.v42934 (state s) (inputs i) = Zmod.unsigned (N.v42934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42934 s i)) at 1.
  unfold R.v42934, N.v42934.
  unfold R.v6, N.v6.
  rewrite ?node_10372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42935 (s : N.State) (i : N.Inputs) :
  R.v42935 (state s) (inputs i) = Zmod.unsigned (N.v42935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42935 s i)) at 1.
  unfold R.v42935, N.v42935.
  rewrite ?node_42933.
  rewrite ?node_42934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42936 (s : N.State) (i : N.Inputs) :
  R.v42936 (state s) (inputs i) = Zmod.unsigned (N.v42936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42936 s i)) at 1.
  unfold R.v42936, N.v42936.
  unfold R.v16484, N.v16484.
  rewrite ?node_42935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42937 (s : N.State) (i : N.Inputs) :
  R.v42937 (state s) (inputs i) = Zmod.unsigned (N.v42937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42937 s i)) at 1.
  unfold R.v42937, N.v42937.
  rewrite ?node_42932.
  rewrite ?node_42936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42938 (s : N.State) (i : N.Inputs) :
  R.v42938 (state s) (inputs i) = Zmod.unsigned (N.v42938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42938 s i)) at 1.
  unfold R.v42938, N.v42938.
  unfold R.v6, N.v6.
  rewrite ?node_42937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42939 (s : N.State) (i : N.Inputs) :
  R.v42939 (state s) (inputs i) = Zmod.unsigned (N.v42939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42939 s i)) at 1.
  unfold R.v42939, N.v42939.
  rewrite ?node_10380.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42940 (s : N.State) (i : N.Inputs) :
  R.v42940 (state s) (inputs i) = Zmod.unsigned (N.v42940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42940 s i)) at 1.
  unfold R.v42940, N.v42940.
  unfold R.v6, N.v6.
  rewrite ?node_10545.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42941 (s : N.State) (i : N.Inputs) :
  R.v42941 (state s) (inputs i) = Zmod.unsigned (N.v42941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42941 s i)) at 1.
  unfold R.v42941, N.v42941.
  rewrite ?node_42939.
  rewrite ?node_42940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42942 (s : N.State) (i : N.Inputs) :
  R.v42942 (state s) (inputs i) = Zmod.unsigned (N.v42942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42942 s i)) at 1.
  unfold R.v42942, N.v42942.
  rewrite ?node_42938.
  rewrite ?node_42941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42943 (s : N.State) (i : N.Inputs) :
  R.v42943 (state s) (inputs i) = Zmod.unsigned (N.v42943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42943 s i)) at 1.
  unfold R.v42943, N.v42943.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42944 (s : N.State) (i : N.Inputs) :
  R.v42944 (state s) (inputs i) = Zmod.unsigned (N.v42944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42944 s i)) at 1.
  unfold R.v42944, N.v42944.
  rewrite ?node_10387.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42945 (s : N.State) (i : N.Inputs) :
  R.v42945 (state s) (inputs i) = Zmod.unsigned (N.v42945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42945 s i)) at 1.
  unfold R.v42945, N.v42945.
  unfold R.v6, N.v6.
  rewrite ?node_10383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42946 (s : N.State) (i : N.Inputs) :
  R.v42946 (state s) (inputs i) = Zmod.unsigned (N.v42946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42946 s i)) at 1.
  unfold R.v42946, N.v42946.
  unfold R.v6, N.v6.
  rewrite ?node_10380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42947 (s : N.State) (i : N.Inputs) :
  R.v42947 (state s) (inputs i) = Zmod.unsigned (N.v42947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42947 s i)) at 1.
  unfold R.v42947, N.v42947.
  rewrite ?node_42945.
  rewrite ?node_42946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42948 (s : N.State) (i : N.Inputs) :
  R.v42948 (state s) (inputs i) = Zmod.unsigned (N.v42948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42948 s i)) at 1.
  unfold R.v42948, N.v42948.
  unfold R.v16484, N.v16484.
  rewrite ?node_42947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42949 (s : N.State) (i : N.Inputs) :
  R.v42949 (state s) (inputs i) = Zmod.unsigned (N.v42949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42949 s i)) at 1.
  unfold R.v42949, N.v42949.
  rewrite ?node_42944.
  rewrite ?node_42948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42950 (s : N.State) (i : N.Inputs) :
  R.v42950 (state s) (inputs i) = Zmod.unsigned (N.v42950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42950 s i)) at 1.
  unfold R.v42950, N.v42950.
  unfold R.v6, N.v6.
  rewrite ?node_42949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42951 (s : N.State) (i : N.Inputs) :
  R.v42951 (state s) (inputs i) = Zmod.unsigned (N.v42951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42951 s i)) at 1.
  unfold R.v42951, N.v42951.
  rewrite ?node_10388.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42952 (s : N.State) (i : N.Inputs) :
  R.v42952 (state s) (inputs i) = Zmod.unsigned (N.v42952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42952 s i)) at 1.
  unfold R.v42952, N.v42952.
  unfold R.v6, N.v6.
  rewrite ?node_10576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42953 (s : N.State) (i : N.Inputs) :
  R.v42953 (state s) (inputs i) = Zmod.unsigned (N.v42953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42953 s i)) at 1.
  unfold R.v42953, N.v42953.
  rewrite ?node_42951.
  rewrite ?node_42952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42954 (s : N.State) (i : N.Inputs) :
  R.v42954 (state s) (inputs i) = Zmod.unsigned (N.v42954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42954 s i)) at 1.
  unfold R.v42954, N.v42954.
  rewrite ?node_42950.
  rewrite ?node_42953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42955 (s : N.State) (i : N.Inputs) :
  R.v42955 (state s) (inputs i) = Zmod.unsigned (N.v42955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42955 s i)) at 1.
  unfold R.v42955, N.v42955.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42956 (s : N.State) (i : N.Inputs) :
  R.v42956 (state s) (inputs i) = Zmod.unsigned (N.v42956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42956 s i)) at 1.
  unfold R.v42956, N.v42956.
  rewrite ?node_10472.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42957 (s : N.State) (i : N.Inputs) :
  R.v42957 (state s) (inputs i) = Zmod.unsigned (N.v42957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42957 s i)) at 1.
  unfold R.v42957, N.v42957.
  rewrite ?node_10468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42958 (s : N.State) (i : N.Inputs) :
  R.v42958 (state s) (inputs i) = Zmod.unsigned (N.v42958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42958 s i)) at 1.
  unfold R.v42958, N.v42958.
  rewrite ?node_10460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42959 (s : N.State) (i : N.Inputs) :
  R.v42959 (state s) (inputs i) = Zmod.unsigned (N.v42959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42959 s i)) at 1.
  unfold R.v42959, N.v42959.
  unfold R.v6, N.v6.
  rewrite ?node_10452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42960 (s : N.State) (i : N.Inputs) :
  R.v42960 (state s) (inputs i) = Zmod.unsigned (N.v42960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42960 s i)) at 1.
  unfold R.v42960, N.v42960.
  unfold R.v6, N.v6.
  rewrite ?node_10445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42961 (s : N.State) (i : N.Inputs) :
  R.v42961 (state s) (inputs i) = Zmod.unsigned (N.v42961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42961 s i)) at 1.
  unfold R.v42961, N.v42961.
  rewrite ?node_42959.
  rewrite ?node_42960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42962 (s : N.State) (i : N.Inputs) :
  R.v42962 (state s) (inputs i) = Zmod.unsigned (N.v42962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42962 s i)) at 1.
  unfold R.v42962, N.v42962.
  unfold R.v16484, N.v16484.
  rewrite ?node_42961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42963 (s : N.State) (i : N.Inputs) :
  R.v42963 (state s) (inputs i) = Zmod.unsigned (N.v42963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42963 s i)) at 1.
  unfold R.v42963, N.v42963.
  rewrite ?node_42956.
  rewrite ?node_42957.
  rewrite ?node_42958.
  rewrite ?node_42962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42964 (s : N.State) (i : N.Inputs) :
  R.v42964 (state s) (inputs i) = Zmod.unsigned (N.v42964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42964 s i)) at 1.
  unfold R.v42964, N.v42964.
  unfold R.v6, N.v6.
  rewrite ?node_42963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42965 (s : N.State) (i : N.Inputs) :
  R.v42965 (state s) (inputs i) = Zmod.unsigned (N.v42965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42965 s i)) at 1.
  unfold R.v42965, N.v42965.
  rewrite ?node_10473.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42966 (s : N.State) (i : N.Inputs) :
  R.v42966 (state s) (inputs i) = Zmod.unsigned (N.v42966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42966 s i)) at 1.
  unfold R.v42966, N.v42966.
  unfold R.v6, N.v6.
  rewrite ?node_10632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42967 (s : N.State) (i : N.Inputs) :
  R.v42967 (state s) (inputs i) = Zmod.unsigned (N.v42967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42967 s i)) at 1.
  unfold R.v42967, N.v42967.
  unfold R.v6, N.v6.
  rewrite ?node_10718.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42968 (s : N.State) (i : N.Inputs) :
  R.v42968 (state s) (inputs i) = Zmod.unsigned (N.v42968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42968 s i)) at 1.
  unfold R.v42968, N.v42968.
  rewrite ?node_42965.
  rewrite ?node_42966.
  rewrite ?node_42967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42969 (s : N.State) (i : N.Inputs) :
  R.v42969 (state s) (inputs i) = Zmod.unsigned (N.v42969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42969 s i)) at 1.
  unfold R.v42969, N.v42969.
  rewrite ?node_42964.
  rewrite ?node_42968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42970 (s : N.State) (i : N.Inputs) :
  R.v42970 (state s) (inputs i) = Zmod.unsigned (N.v42970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42970 s i)) at 1.
  unfold R.v42970, N.v42970.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42971 (s : N.State) (i : N.Inputs) :
  R.v42971 (state s) (inputs i) = Zmod.unsigned (N.v42971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42971 s i)) at 1.
  unfold R.v42971, N.v42971.
  rewrite ?node_10460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42972 (s : N.State) (i : N.Inputs) :
  R.v42972 (state s) (inputs i) = Zmod.unsigned (N.v42972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42972 s i)) at 1.
  unfold R.v42972, N.v42972.
  unfold R.v6, N.v6.
  rewrite ?node_10452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42973 (s : N.State) (i : N.Inputs) :
  R.v42973 (state s) (inputs i) = Zmod.unsigned (N.v42973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42973 s i)) at 1.
  unfold R.v42973, N.v42973.
  unfold R.v6, N.v6.
  rewrite ?node_10445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42974 (s : N.State) (i : N.Inputs) :
  R.v42974 (state s) (inputs i) = Zmod.unsigned (N.v42974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42974 s i)) at 1.
  unfold R.v42974, N.v42974.
  rewrite ?node_42972.
  rewrite ?node_42973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42975 (s : N.State) (i : N.Inputs) :
  R.v42975 (state s) (inputs i) = Zmod.unsigned (N.v42975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42975 s i)) at 1.
  unfold R.v42975, N.v42975.
  unfold R.v16484, N.v16484.
  rewrite ?node_42974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42976 (s : N.State) (i : N.Inputs) :
  R.v42976 (state s) (inputs i) = Zmod.unsigned (N.v42976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42976 s i)) at 1.
  unfold R.v42976, N.v42976.
  rewrite ?node_42971.
  rewrite ?node_42975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42977 (s : N.State) (i : N.Inputs) :
  R.v42977 (state s) (inputs i) = Zmod.unsigned (N.v42977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42977 s i)) at 1.
  unfold R.v42977, N.v42977.
  unfold R.v6, N.v6.
  rewrite ?node_42976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42978 (s : N.State) (i : N.Inputs) :
  R.v42978 (state s) (inputs i) = Zmod.unsigned (N.v42978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42978 s i)) at 1.
  unfold R.v42978, N.v42978.
  rewrite ?node_10461.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42979 (s : N.State) (i : N.Inputs) :
  R.v42979 (state s) (inputs i) = Zmod.unsigned (N.v42979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42979 s i)) at 1.
  unfold R.v42979, N.v42979.
  unfold R.v6, N.v6.
  rewrite ?node_10632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42980 (s : N.State) (i : N.Inputs) :
  R.v42980 (state s) (inputs i) = Zmod.unsigned (N.v42980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42980 s i)) at 1.
  unfold R.v42980, N.v42980.
  rewrite ?node_42978.
  rewrite ?node_42979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42981 (s : N.State) (i : N.Inputs) :
  R.v42981 (state s) (inputs i) = Zmod.unsigned (N.v42981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42981 s i)) at 1.
  unfold R.v42981, N.v42981.
  rewrite ?node_42977.
  rewrite ?node_42980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42982 (s : N.State) (i : N.Inputs) :
  R.v42982 (state s) (inputs i) = Zmod.unsigned (N.v42982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42982 s i)) at 1.
  unfold R.v42982, N.v42982.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42983 (s : N.State) (i : N.Inputs) :
  R.v42983 (state s) (inputs i) = Zmod.unsigned (N.v42983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42983 s i)) at 1.
  unfold R.v42983, N.v42983.
  rewrite ?node_10472.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42984 (s : N.State) (i : N.Inputs) :
  R.v42984 (state s) (inputs i) = Zmod.unsigned (N.v42984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42984 s i)) at 1.
  unfold R.v42984, N.v42984.
  unfold R.v6, N.v6.
  rewrite ?node_10468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42985 (s : N.State) (i : N.Inputs) :
  R.v42985 (state s) (inputs i) = Zmod.unsigned (N.v42985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42985 s i)) at 1.
  unfold R.v42985, N.v42985.
  unfold R.v6, N.v6.
  rewrite ?node_10461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42986 (s : N.State) (i : N.Inputs) :
  R.v42986 (state s) (inputs i) = Zmod.unsigned (N.v42986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42986 s i)) at 1.
  unfold R.v42986, N.v42986.
  rewrite ?node_42984.
  rewrite ?node_42985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42987 (s : N.State) (i : N.Inputs) :
  R.v42987 (state s) (inputs i) = Zmod.unsigned (N.v42987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42987 s i)) at 1.
  unfold R.v42987, N.v42987.
  unfold R.v16484, N.v16484.
  rewrite ?node_42986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42988 (s : N.State) (i : N.Inputs) :
  R.v42988 (state s) (inputs i) = Zmod.unsigned (N.v42988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42988 s i)) at 1.
  unfold R.v42988, N.v42988.
  rewrite ?node_42983.
  rewrite ?node_42987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42989 (s : N.State) (i : N.Inputs) :
  R.v42989 (state s) (inputs i) = Zmod.unsigned (N.v42989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42989 s i)) at 1.
  unfold R.v42989, N.v42989.
  unfold R.v6, N.v6.
  rewrite ?node_42988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42990 (s : N.State) (i : N.Inputs) :
  R.v42990 (state s) (inputs i) = Zmod.unsigned (N.v42990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42990 s i)) at 1.
  unfold R.v42990, N.v42990.
  rewrite ?node_10473.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42991 (s : N.State) (i : N.Inputs) :
  R.v42991 (state s) (inputs i) = Zmod.unsigned (N.v42991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42991 s i)) at 1.
  unfold R.v42991, N.v42991.
  unfold R.v6, N.v6.
  rewrite ?node_10718.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42992 (s : N.State) (i : N.Inputs) :
  R.v42992 (state s) (inputs i) = Zmod.unsigned (N.v42992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42992 s i)) at 1.
  unfold R.v42992, N.v42992.
  rewrite ?node_42990.
  rewrite ?node_42991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42993 (s : N.State) (i : N.Inputs) :
  R.v42993 (state s) (inputs i) = Zmod.unsigned (N.v42993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42993 s i)) at 1.
  unfold R.v42993, N.v42993.
  rewrite ?node_42989.
  rewrite ?node_42992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42994 (s : N.State) (i : N.Inputs) :
  R.v42994 (state s) (inputs i) = Zmod.unsigned (N.v42994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42994 s i)) at 1.
  unfold R.v42994, N.v42994.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42995 (s : N.State) (i : N.Inputs) :
  R.v42995 (state s) (inputs i) = Zmod.unsigned (N.v42995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42995 s i)) at 1.
  unfold R.v42995, N.v42995.
  rewrite ?node_10507.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42996 (s : N.State) (i : N.Inputs) :
  R.v42996 (state s) (inputs i) = Zmod.unsigned (N.v42996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42996 s i)) at 1.
  unfold R.v42996, N.v42996.
  rewrite ?node_10503.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42997 (s : N.State) (i : N.Inputs) :
  R.v42997 (state s) (inputs i) = Zmod.unsigned (N.v42997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42997 s i)) at 1.
  unfold R.v42997, N.v42997.
  rewrite ?node_10495.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42998 (s : N.State) (i : N.Inputs) :
  R.v42998 (state s) (inputs i) = Zmod.unsigned (N.v42998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42998 s i)) at 1.
  unfold R.v42998, N.v42998.
  unfold R.v6, N.v6.
  rewrite ?node_10487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42999 (s : N.State) (i : N.Inputs) :
  R.v42999 (state s) (inputs i) = Zmod.unsigned (N.v42999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42999 s i)) at 1.
  unfold R.v42999, N.v42999.
  unfold R.v6, N.v6.
  rewrite ?node_10480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
