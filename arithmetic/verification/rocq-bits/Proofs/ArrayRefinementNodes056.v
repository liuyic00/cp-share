(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes055.
Lemma node_56000 (s : N.State) (i : N.Inputs) :
  R.v56000 (state s) (inputs i) = Zmod.unsigned (N.v56000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56000 s i)) at 1.
  unfold R.v56000, N.v56000.
  rewrite ?node_11220.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56001 (s : N.State) (i : N.Inputs) :
  R.v56001 (state s) (inputs i) = Zmod.unsigned (N.v56001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56001 s i)) at 1.
  unfold R.v56001, N.v56001.
  unfold R.v6, N.v6.
  rewrite ?node_11381.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56002 (s : N.State) (i : N.Inputs) :
  R.v56002 (state s) (inputs i) = Zmod.unsigned (N.v56002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56002 s i)) at 1.
  unfold R.v56002, N.v56002.
  rewrite ?node_56000.
  rewrite ?node_56001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56003 (s : N.State) (i : N.Inputs) :
  R.v56003 (state s) (inputs i) = Zmod.unsigned (N.v56003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56003 s i)) at 1.
  unfold R.v56003, N.v56003.
  rewrite ?node_55999.
  rewrite ?node_56002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56004 (s : N.State) (i : N.Inputs) :
  R.v56004 (state s) (inputs i) = Zmod.unsigned (N.v56004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56004 s i)) at 1.
  unfold R.v56004, N.v56004.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56005 (s : N.State) (i : N.Inputs) :
  R.v56005 (state s) (inputs i) = Zmod.unsigned (N.v56005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56005 s i)) at 1.
  unfold R.v56005, N.v56005.
  rewrite ?node_11227.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56006 (s : N.State) (i : N.Inputs) :
  R.v56006 (state s) (inputs i) = Zmod.unsigned (N.v56006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56006 s i)) at 1.
  unfold R.v56006, N.v56006.
  unfold R.v6, N.v6.
  rewrite ?node_11223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56007 (s : N.State) (i : N.Inputs) :
  R.v56007 (state s) (inputs i) = Zmod.unsigned (N.v56007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56007 s i)) at 1.
  unfold R.v56007, N.v56007.
  unfold R.v6, N.v6.
  rewrite ?node_11220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56008 (s : N.State) (i : N.Inputs) :
  R.v56008 (state s) (inputs i) = Zmod.unsigned (N.v56008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56008 s i)) at 1.
  unfold R.v56008, N.v56008.
  rewrite ?node_56006.
  rewrite ?node_56007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56009 (s : N.State) (i : N.Inputs) :
  R.v56009 (state s) (inputs i) = Zmod.unsigned (N.v56009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56009 s i)) at 1.
  unfold R.v56009, N.v56009.
  unfold R.v16484, N.v16484.
  rewrite ?node_56008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56010 (s : N.State) (i : N.Inputs) :
  R.v56010 (state s) (inputs i) = Zmod.unsigned (N.v56010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56010 s i)) at 1.
  unfold R.v56010, N.v56010.
  rewrite ?node_56005.
  rewrite ?node_56009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56011 (s : N.State) (i : N.Inputs) :
  R.v56011 (state s) (inputs i) = Zmod.unsigned (N.v56011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56011 s i)) at 1.
  unfold R.v56011, N.v56011.
  unfold R.v6, N.v6.
  rewrite ?node_56010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56012 (s : N.State) (i : N.Inputs) :
  R.v56012 (state s) (inputs i) = Zmod.unsigned (N.v56012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56012 s i)) at 1.
  unfold R.v56012, N.v56012.
  rewrite ?node_11228.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56013 (s : N.State) (i : N.Inputs) :
  R.v56013 (state s) (inputs i) = Zmod.unsigned (N.v56013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56013 s i)) at 1.
  unfold R.v56013, N.v56013.
  unfold R.v6, N.v6.
  rewrite ?node_11389.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56014 (s : N.State) (i : N.Inputs) :
  R.v56014 (state s) (inputs i) = Zmod.unsigned (N.v56014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56014 s i)) at 1.
  unfold R.v56014, N.v56014.
  rewrite ?node_56012.
  rewrite ?node_56013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56015 (s : N.State) (i : N.Inputs) :
  R.v56015 (state s) (inputs i) = Zmod.unsigned (N.v56015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56015 s i)) at 1.
  unfold R.v56015, N.v56015.
  rewrite ?node_56011.
  rewrite ?node_56014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56016 (s : N.State) (i : N.Inputs) :
  R.v56016 (state s) (inputs i) = Zmod.unsigned (N.v56016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56016 s i)) at 1.
  unfold R.v56016, N.v56016.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56017 (s : N.State) (i : N.Inputs) :
  R.v56017 (state s) (inputs i) = Zmod.unsigned (N.v56017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56017 s i)) at 1.
  unfold R.v56017, N.v56017.
  rewrite ?node_11381.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56018 (s : N.State) (i : N.Inputs) :
  R.v56018 (state s) (inputs i) = Zmod.unsigned (N.v56018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56018 s i)) at 1.
  unfold R.v56018, N.v56018.
  rewrite ?node_11377.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56019 (s : N.State) (i : N.Inputs) :
  R.v56019 (state s) (inputs i) = Zmod.unsigned (N.v56019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56019 s i)) at 1.
  unfold R.v56019, N.v56019.
  rewrite ?node_11373.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56020 (s : N.State) (i : N.Inputs) :
  R.v56020 (state s) (inputs i) = Zmod.unsigned (N.v56020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56020 s i)) at 1.
  unfold R.v56020, N.v56020.
  unfold R.v6, N.v6.
  rewrite ?node_11369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56021 (s : N.State) (i : N.Inputs) :
  R.v56021 (state s) (inputs i) = Zmod.unsigned (N.v56021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56021 s i)) at 1.
  unfold R.v56021, N.v56021.
  unfold R.v6, N.v6.
  rewrite ?node_11350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56022 (s : N.State) (i : N.Inputs) :
  R.v56022 (state s) (inputs i) = Zmod.unsigned (N.v56022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56022 s i)) at 1.
  unfold R.v56022, N.v56022.
  rewrite ?node_56020.
  rewrite ?node_56021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56023 (s : N.State) (i : N.Inputs) :
  R.v56023 (state s) (inputs i) = Zmod.unsigned (N.v56023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56023 s i)) at 1.
  unfold R.v56023, N.v56023.
  unfold R.v16484, N.v16484.
  rewrite ?node_56022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56024 (s : N.State) (i : N.Inputs) :
  R.v56024 (state s) (inputs i) = Zmod.unsigned (N.v56024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56024 s i)) at 1.
  unfold R.v56024, N.v56024.
  rewrite ?node_56017.
  rewrite ?node_56018.
  rewrite ?node_56019.
  rewrite ?node_56023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56025 (s : N.State) (i : N.Inputs) :
  R.v56025 (state s) (inputs i) = Zmod.unsigned (N.v56025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56025 s i)) at 1.
  unfold R.v56025, N.v56025.
  unfold R.v6, N.v6.
  rewrite ?node_56024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56026 (s : N.State) (i : N.Inputs) :
  R.v56026 (state s) (inputs i) = Zmod.unsigned (N.v56026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56026 s i)) at 1.
  unfold R.v56026, N.v56026.
  rewrite ?node_11382.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56027 (s : N.State) (i : N.Inputs) :
  R.v56027 (state s) (inputs i) = Zmod.unsigned (N.v56027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56027 s i)) at 1.
  unfold R.v56027, N.v56027.
  unfold R.v6, N.v6.
  rewrite ?node_11536.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56028 (s : N.State) (i : N.Inputs) :
  R.v56028 (state s) (inputs i) = Zmod.unsigned (N.v56028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56028 s i)) at 1.
  unfold R.v56028, N.v56028.
  unfold R.v6, N.v6.
  rewrite ?node_11540.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56029 (s : N.State) (i : N.Inputs) :
  R.v56029 (state s) (inputs i) = Zmod.unsigned (N.v56029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56029 s i)) at 1.
  unfold R.v56029, N.v56029.
  rewrite ?node_56026.
  rewrite ?node_56027.
  rewrite ?node_56028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56030 (s : N.State) (i : N.Inputs) :
  R.v56030 (state s) (inputs i) = Zmod.unsigned (N.v56030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56030 s i)) at 1.
  unfold R.v56030, N.v56030.
  rewrite ?node_56025.
  rewrite ?node_56029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56031 (s : N.State) (i : N.Inputs) :
  R.v56031 (state s) (inputs i) = Zmod.unsigned (N.v56031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56031 s i)) at 1.
  unfold R.v56031, N.v56031.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56032 (s : N.State) (i : N.Inputs) :
  R.v56032 (state s) (inputs i) = Zmod.unsigned (N.v56032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56032 s i)) at 1.
  unfold R.v56032, N.v56032.
  rewrite ?node_11373.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56033 (s : N.State) (i : N.Inputs) :
  R.v56033 (state s) (inputs i) = Zmod.unsigned (N.v56033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56033 s i)) at 1.
  unfold R.v56033, N.v56033.
  unfold R.v6, N.v6.
  rewrite ?node_11369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56034 (s : N.State) (i : N.Inputs) :
  R.v56034 (state s) (inputs i) = Zmod.unsigned (N.v56034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56034 s i)) at 1.
  unfold R.v56034, N.v56034.
  unfold R.v6, N.v6.
  rewrite ?node_11350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56035 (s : N.State) (i : N.Inputs) :
  R.v56035 (state s) (inputs i) = Zmod.unsigned (N.v56035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56035 s i)) at 1.
  unfold R.v56035, N.v56035.
  rewrite ?node_56033.
  rewrite ?node_56034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56036 (s : N.State) (i : N.Inputs) :
  R.v56036 (state s) (inputs i) = Zmod.unsigned (N.v56036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56036 s i)) at 1.
  unfold R.v56036, N.v56036.
  unfold R.v16484, N.v16484.
  rewrite ?node_56035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56037 (s : N.State) (i : N.Inputs) :
  R.v56037 (state s) (inputs i) = Zmod.unsigned (N.v56037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56037 s i)) at 1.
  unfold R.v56037, N.v56037.
  rewrite ?node_56032.
  rewrite ?node_56036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56038 (s : N.State) (i : N.Inputs) :
  R.v56038 (state s) (inputs i) = Zmod.unsigned (N.v56038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56038 s i)) at 1.
  unfold R.v56038, N.v56038.
  unfold R.v6, N.v6.
  rewrite ?node_56037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56039 (s : N.State) (i : N.Inputs) :
  R.v56039 (state s) (inputs i) = Zmod.unsigned (N.v56039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56039 s i)) at 1.
  unfold R.v56039, N.v56039.
  rewrite ?node_11374.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56040 (s : N.State) (i : N.Inputs) :
  R.v56040 (state s) (inputs i) = Zmod.unsigned (N.v56040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56040 s i)) at 1.
  unfold R.v56040, N.v56040.
  unfold R.v6, N.v6.
  rewrite ?node_11536.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56041 (s : N.State) (i : N.Inputs) :
  R.v56041 (state s) (inputs i) = Zmod.unsigned (N.v56041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56041 s i)) at 1.
  unfold R.v56041, N.v56041.
  rewrite ?node_56039.
  rewrite ?node_56040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56042 (s : N.State) (i : N.Inputs) :
  R.v56042 (state s) (inputs i) = Zmod.unsigned (N.v56042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56042 s i)) at 1.
  unfold R.v56042, N.v56042.
  rewrite ?node_56038.
  rewrite ?node_56041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56043 (s : N.State) (i : N.Inputs) :
  R.v56043 (state s) (inputs i) = Zmod.unsigned (N.v56043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56043 s i)) at 1.
  unfold R.v56043, N.v56043.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56044 (s : N.State) (i : N.Inputs) :
  R.v56044 (state s) (inputs i) = Zmod.unsigned (N.v56044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56044 s i)) at 1.
  unfold R.v56044, N.v56044.
  rewrite ?node_11381.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56045 (s : N.State) (i : N.Inputs) :
  R.v56045 (state s) (inputs i) = Zmod.unsigned (N.v56045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56045 s i)) at 1.
  unfold R.v56045, N.v56045.
  unfold R.v6, N.v6.
  rewrite ?node_11377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56046 (s : N.State) (i : N.Inputs) :
  R.v56046 (state s) (inputs i) = Zmod.unsigned (N.v56046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56046 s i)) at 1.
  unfold R.v56046, N.v56046.
  unfold R.v6, N.v6.
  rewrite ?node_11374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56047 (s : N.State) (i : N.Inputs) :
  R.v56047 (state s) (inputs i) = Zmod.unsigned (N.v56047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56047 s i)) at 1.
  unfold R.v56047, N.v56047.
  rewrite ?node_56045.
  rewrite ?node_56046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56048 (s : N.State) (i : N.Inputs) :
  R.v56048 (state s) (inputs i) = Zmod.unsigned (N.v56048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56048 s i)) at 1.
  unfold R.v56048, N.v56048.
  unfold R.v16484, N.v16484.
  rewrite ?node_56047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56049 (s : N.State) (i : N.Inputs) :
  R.v56049 (state s) (inputs i) = Zmod.unsigned (N.v56049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56049 s i)) at 1.
  unfold R.v56049, N.v56049.
  rewrite ?node_56044.
  rewrite ?node_56048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56050 (s : N.State) (i : N.Inputs) :
  R.v56050 (state s) (inputs i) = Zmod.unsigned (N.v56050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56050 s i)) at 1.
  unfold R.v56050, N.v56050.
  unfold R.v6, N.v6.
  rewrite ?node_56049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56051 (s : N.State) (i : N.Inputs) :
  R.v56051 (state s) (inputs i) = Zmod.unsigned (N.v56051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56051 s i)) at 1.
  unfold R.v56051, N.v56051.
  rewrite ?node_11382.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56052 (s : N.State) (i : N.Inputs) :
  R.v56052 (state s) (inputs i) = Zmod.unsigned (N.v56052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56052 s i)) at 1.
  unfold R.v56052, N.v56052.
  unfold R.v6, N.v6.
  rewrite ?node_11540.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56053 (s : N.State) (i : N.Inputs) :
  R.v56053 (state s) (inputs i) = Zmod.unsigned (N.v56053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56053 s i)) at 1.
  unfold R.v56053, N.v56053.
  rewrite ?node_56051.
  rewrite ?node_56052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56054 (s : N.State) (i : N.Inputs) :
  R.v56054 (state s) (inputs i) = Zmod.unsigned (N.v56054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56054 s i)) at 1.
  unfold R.v56054, N.v56054.
  rewrite ?node_56050.
  rewrite ?node_56053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56055 (s : N.State) (i : N.Inputs) :
  R.v56055 (state s) (inputs i) = Zmod.unsigned (N.v56055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56055 s i)) at 1.
  unfold R.v56055, N.v56055.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56056 (s : N.State) (i : N.Inputs) :
  R.v56056 (state s) (inputs i) = Zmod.unsigned (N.v56056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56056 s i)) at 1.
  unfold R.v56056, N.v56056.
  rewrite ?node_11536.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56057 (s : N.State) (i : N.Inputs) :
  R.v56057 (state s) (inputs i) = Zmod.unsigned (N.v56057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56057 s i)) at 1.
  unfold R.v56057, N.v56057.
  rewrite ?node_11532.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56058 (s : N.State) (i : N.Inputs) :
  R.v56058 (state s) (inputs i) = Zmod.unsigned (N.v56058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56058 s i)) at 1.
  unfold R.v56058, N.v56058.
  rewrite ?node_11528.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56059 (s : N.State) (i : N.Inputs) :
  R.v56059 (state s) (inputs i) = Zmod.unsigned (N.v56059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56059 s i)) at 1.
  unfold R.v56059, N.v56059.
  unfold R.v6, N.v6.
  rewrite ?node_11524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56060 (s : N.State) (i : N.Inputs) :
  R.v56060 (state s) (inputs i) = Zmod.unsigned (N.v56060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56060 s i)) at 1.
  unfold R.v56060, N.v56060.
  unfold R.v6, N.v6.
  rewrite ?node_11505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56061 (s : N.State) (i : N.Inputs) :
  R.v56061 (state s) (inputs i) = Zmod.unsigned (N.v56061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56061 s i)) at 1.
  unfold R.v56061, N.v56061.
  rewrite ?node_56059.
  rewrite ?node_56060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56062 (s : N.State) (i : N.Inputs) :
  R.v56062 (state s) (inputs i) = Zmod.unsigned (N.v56062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56062 s i)) at 1.
  unfold R.v56062, N.v56062.
  unfold R.v16484, N.v16484.
  rewrite ?node_56061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56063 (s : N.State) (i : N.Inputs) :
  R.v56063 (state s) (inputs i) = Zmod.unsigned (N.v56063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56063 s i)) at 1.
  unfold R.v56063, N.v56063.
  rewrite ?node_56056.
  rewrite ?node_56057.
  rewrite ?node_56058.
  rewrite ?node_56062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56064 (s : N.State) (i : N.Inputs) :
  R.v56064 (state s) (inputs i) = Zmod.unsigned (N.v56064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56064 s i)) at 1.
  unfold R.v56064, N.v56064.
  unfold R.v6, N.v6.
  rewrite ?node_56063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56065 (s : N.State) (i : N.Inputs) :
  R.v56065 (state s) (inputs i) = Zmod.unsigned (N.v56065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56065 s i)) at 1.
  unfold R.v56065, N.v56065.
  rewrite ?node_11537.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56066 (s : N.State) (i : N.Inputs) :
  R.v56066 (state s) (inputs i) = Zmod.unsigned (N.v56066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56066 s i)) at 1.
  unfold R.v56066, N.v56066.
  unfold R.v6, N.v6.
  rewrite ?node_11685.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56067 (s : N.State) (i : N.Inputs) :
  R.v56067 (state s) (inputs i) = Zmod.unsigned (N.v56067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56067 s i)) at 1.
  unfold R.v56067, N.v56067.
  unfold R.v6, N.v6.
  rewrite ?node_11689.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56068 (s : N.State) (i : N.Inputs) :
  R.v56068 (state s) (inputs i) = Zmod.unsigned (N.v56068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56068 s i)) at 1.
  unfold R.v56068, N.v56068.
  rewrite ?node_56065.
  rewrite ?node_56066.
  rewrite ?node_56067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56069 (s : N.State) (i : N.Inputs) :
  R.v56069 (state s) (inputs i) = Zmod.unsigned (N.v56069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56069 s i)) at 1.
  unfold R.v56069, N.v56069.
  rewrite ?node_56064.
  rewrite ?node_56068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56070 (s : N.State) (i : N.Inputs) :
  R.v56070 (state s) (inputs i) = Zmod.unsigned (N.v56070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56070 s i)) at 1.
  unfold R.v56070, N.v56070.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56071 (s : N.State) (i : N.Inputs) :
  R.v56071 (state s) (inputs i) = Zmod.unsigned (N.v56071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56071 s i)) at 1.
  unfold R.v56071, N.v56071.
  rewrite ?node_11528.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56072 (s : N.State) (i : N.Inputs) :
  R.v56072 (state s) (inputs i) = Zmod.unsigned (N.v56072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56072 s i)) at 1.
  unfold R.v56072, N.v56072.
  unfold R.v6, N.v6.
  rewrite ?node_11524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56073 (s : N.State) (i : N.Inputs) :
  R.v56073 (state s) (inputs i) = Zmod.unsigned (N.v56073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56073 s i)) at 1.
  unfold R.v56073, N.v56073.
  unfold R.v6, N.v6.
  rewrite ?node_11505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56074 (s : N.State) (i : N.Inputs) :
  R.v56074 (state s) (inputs i) = Zmod.unsigned (N.v56074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56074 s i)) at 1.
  unfold R.v56074, N.v56074.
  rewrite ?node_56072.
  rewrite ?node_56073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56075 (s : N.State) (i : N.Inputs) :
  R.v56075 (state s) (inputs i) = Zmod.unsigned (N.v56075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56075 s i)) at 1.
  unfold R.v56075, N.v56075.
  unfold R.v16484, N.v16484.
  rewrite ?node_56074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56076 (s : N.State) (i : N.Inputs) :
  R.v56076 (state s) (inputs i) = Zmod.unsigned (N.v56076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56076 s i)) at 1.
  unfold R.v56076, N.v56076.
  rewrite ?node_56071.
  rewrite ?node_56075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56077 (s : N.State) (i : N.Inputs) :
  R.v56077 (state s) (inputs i) = Zmod.unsigned (N.v56077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56077 s i)) at 1.
  unfold R.v56077, N.v56077.
  unfold R.v6, N.v6.
  rewrite ?node_56076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56078 (s : N.State) (i : N.Inputs) :
  R.v56078 (state s) (inputs i) = Zmod.unsigned (N.v56078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56078 s i)) at 1.
  unfold R.v56078, N.v56078.
  rewrite ?node_11529.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56079 (s : N.State) (i : N.Inputs) :
  R.v56079 (state s) (inputs i) = Zmod.unsigned (N.v56079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56079 s i)) at 1.
  unfold R.v56079, N.v56079.
  unfold R.v6, N.v6.
  rewrite ?node_11685.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56080 (s : N.State) (i : N.Inputs) :
  R.v56080 (state s) (inputs i) = Zmod.unsigned (N.v56080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56080 s i)) at 1.
  unfold R.v56080, N.v56080.
  rewrite ?node_56078.
  rewrite ?node_56079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56081 (s : N.State) (i : N.Inputs) :
  R.v56081 (state s) (inputs i) = Zmod.unsigned (N.v56081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56081 s i)) at 1.
  unfold R.v56081, N.v56081.
  rewrite ?node_56077.
  rewrite ?node_56080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56082 (s : N.State) (i : N.Inputs) :
  R.v56082 (state s) (inputs i) = Zmod.unsigned (N.v56082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56082 s i)) at 1.
  unfold R.v56082, N.v56082.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56083 (s : N.State) (i : N.Inputs) :
  R.v56083 (state s) (inputs i) = Zmod.unsigned (N.v56083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56083 s i)) at 1.
  unfold R.v56083, N.v56083.
  rewrite ?node_11536.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56084 (s : N.State) (i : N.Inputs) :
  R.v56084 (state s) (inputs i) = Zmod.unsigned (N.v56084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56084 s i)) at 1.
  unfold R.v56084, N.v56084.
  unfold R.v6, N.v6.
  rewrite ?node_11532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56085 (s : N.State) (i : N.Inputs) :
  R.v56085 (state s) (inputs i) = Zmod.unsigned (N.v56085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56085 s i)) at 1.
  unfold R.v56085, N.v56085.
  unfold R.v6, N.v6.
  rewrite ?node_11529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56086 (s : N.State) (i : N.Inputs) :
  R.v56086 (state s) (inputs i) = Zmod.unsigned (N.v56086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56086 s i)) at 1.
  unfold R.v56086, N.v56086.
  rewrite ?node_56084.
  rewrite ?node_56085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56087 (s : N.State) (i : N.Inputs) :
  R.v56087 (state s) (inputs i) = Zmod.unsigned (N.v56087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56087 s i)) at 1.
  unfold R.v56087, N.v56087.
  unfold R.v16484, N.v16484.
  rewrite ?node_56086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56088 (s : N.State) (i : N.Inputs) :
  R.v56088 (state s) (inputs i) = Zmod.unsigned (N.v56088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56088 s i)) at 1.
  unfold R.v56088, N.v56088.
  rewrite ?node_56083.
  rewrite ?node_56087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56089 (s : N.State) (i : N.Inputs) :
  R.v56089 (state s) (inputs i) = Zmod.unsigned (N.v56089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56089 s i)) at 1.
  unfold R.v56089, N.v56089.
  unfold R.v6, N.v6.
  rewrite ?node_56088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56090 (s : N.State) (i : N.Inputs) :
  R.v56090 (state s) (inputs i) = Zmod.unsigned (N.v56090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56090 s i)) at 1.
  unfold R.v56090, N.v56090.
  rewrite ?node_11537.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56091 (s : N.State) (i : N.Inputs) :
  R.v56091 (state s) (inputs i) = Zmod.unsigned (N.v56091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56091 s i)) at 1.
  unfold R.v56091, N.v56091.
  unfold R.v6, N.v6.
  rewrite ?node_11689.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56092 (s : N.State) (i : N.Inputs) :
  R.v56092 (state s) (inputs i) = Zmod.unsigned (N.v56092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56092 s i)) at 1.
  unfold R.v56092, N.v56092.
  rewrite ?node_56090.
  rewrite ?node_56091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56093 (s : N.State) (i : N.Inputs) :
  R.v56093 (state s) (inputs i) = Zmod.unsigned (N.v56093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56093 s i)) at 1.
  unfold R.v56093, N.v56093.
  rewrite ?node_56089.
  rewrite ?node_56092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56094 (s : N.State) (i : N.Inputs) :
  R.v56094 (state s) (inputs i) = Zmod.unsigned (N.v56094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56094 s i)) at 1.
  unfold R.v56094, N.v56094.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56095 (s : N.State) (i : N.Inputs) :
  R.v56095 (state s) (inputs i) = Zmod.unsigned (N.v56095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56095 s i)) at 1.
  unfold R.v56095, N.v56095.
  rewrite ?node_11685.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56096 (s : N.State) (i : N.Inputs) :
  R.v56096 (state s) (inputs i) = Zmod.unsigned (N.v56096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56096 s i)) at 1.
  unfold R.v56096, N.v56096.
  rewrite ?node_11681.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56097 (s : N.State) (i : N.Inputs) :
  R.v56097 (state s) (inputs i) = Zmod.unsigned (N.v56097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56097 s i)) at 1.
  unfold R.v56097, N.v56097.
  rewrite ?node_11677.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56098 (s : N.State) (i : N.Inputs) :
  R.v56098 (state s) (inputs i) = Zmod.unsigned (N.v56098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56098 s i)) at 1.
  unfold R.v56098, N.v56098.
  unfold R.v6, N.v6.
  rewrite ?node_11673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56099 (s : N.State) (i : N.Inputs) :
  R.v56099 (state s) (inputs i) = Zmod.unsigned (N.v56099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56099 s i)) at 1.
  unfold R.v56099, N.v56099.
  unfold R.v6, N.v6.
  rewrite ?node_11654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56100 (s : N.State) (i : N.Inputs) :
  R.v56100 (state s) (inputs i) = Zmod.unsigned (N.v56100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56100 s i)) at 1.
  unfold R.v56100, N.v56100.
  rewrite ?node_56098.
  rewrite ?node_56099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56101 (s : N.State) (i : N.Inputs) :
  R.v56101 (state s) (inputs i) = Zmod.unsigned (N.v56101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56101 s i)) at 1.
  unfold R.v56101, N.v56101.
  unfold R.v16484, N.v16484.
  rewrite ?node_56100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56102 (s : N.State) (i : N.Inputs) :
  R.v56102 (state s) (inputs i) = Zmod.unsigned (N.v56102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56102 s i)) at 1.
  unfold R.v56102, N.v56102.
  rewrite ?node_56095.
  rewrite ?node_56096.
  rewrite ?node_56097.
  rewrite ?node_56101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56103 (s : N.State) (i : N.Inputs) :
  R.v56103 (state s) (inputs i) = Zmod.unsigned (N.v56103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56103 s i)) at 1.
  unfold R.v56103, N.v56103.
  unfold R.v6, N.v6.
  rewrite ?node_56102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56104 (s : N.State) (i : N.Inputs) :
  R.v56104 (state s) (inputs i) = Zmod.unsigned (N.v56104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56104 s i)) at 1.
  unfold R.v56104, N.v56104.
  rewrite ?node_11686.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56105 (s : N.State) (i : N.Inputs) :
  R.v56105 (state s) (inputs i) = Zmod.unsigned (N.v56105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56105 s i)) at 1.
  unfold R.v56105, N.v56105.
  unfold R.v6, N.v6.
  rewrite ?node_11831.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56106 (s : N.State) (i : N.Inputs) :
  R.v56106 (state s) (inputs i) = Zmod.unsigned (N.v56106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56106 s i)) at 1.
  unfold R.v56106, N.v56106.
  unfold R.v6, N.v6.
  rewrite ?node_11835.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56107 (s : N.State) (i : N.Inputs) :
  R.v56107 (state s) (inputs i) = Zmod.unsigned (N.v56107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56107 s i)) at 1.
  unfold R.v56107, N.v56107.
  rewrite ?node_56104.
  rewrite ?node_56105.
  rewrite ?node_56106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56108 (s : N.State) (i : N.Inputs) :
  R.v56108 (state s) (inputs i) = Zmod.unsigned (N.v56108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56108 s i)) at 1.
  unfold R.v56108, N.v56108.
  rewrite ?node_56103.
  rewrite ?node_56107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56109 (s : N.State) (i : N.Inputs) :
  R.v56109 (state s) (inputs i) = Zmod.unsigned (N.v56109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56109 s i)) at 1.
  unfold R.v56109, N.v56109.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56110 (s : N.State) (i : N.Inputs) :
  R.v56110 (state s) (inputs i) = Zmod.unsigned (N.v56110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56110 s i)) at 1.
  unfold R.v56110, N.v56110.
  rewrite ?node_11677.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56111 (s : N.State) (i : N.Inputs) :
  R.v56111 (state s) (inputs i) = Zmod.unsigned (N.v56111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56111 s i)) at 1.
  unfold R.v56111, N.v56111.
  unfold R.v6, N.v6.
  rewrite ?node_11673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56112 (s : N.State) (i : N.Inputs) :
  R.v56112 (state s) (inputs i) = Zmod.unsigned (N.v56112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56112 s i)) at 1.
  unfold R.v56112, N.v56112.
  unfold R.v6, N.v6.
  rewrite ?node_11654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56113 (s : N.State) (i : N.Inputs) :
  R.v56113 (state s) (inputs i) = Zmod.unsigned (N.v56113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56113 s i)) at 1.
  unfold R.v56113, N.v56113.
  rewrite ?node_56111.
  rewrite ?node_56112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56114 (s : N.State) (i : N.Inputs) :
  R.v56114 (state s) (inputs i) = Zmod.unsigned (N.v56114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56114 s i)) at 1.
  unfold R.v56114, N.v56114.
  unfold R.v16484, N.v16484.
  rewrite ?node_56113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56115 (s : N.State) (i : N.Inputs) :
  R.v56115 (state s) (inputs i) = Zmod.unsigned (N.v56115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56115 s i)) at 1.
  unfold R.v56115, N.v56115.
  rewrite ?node_56110.
  rewrite ?node_56114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56116 (s : N.State) (i : N.Inputs) :
  R.v56116 (state s) (inputs i) = Zmod.unsigned (N.v56116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56116 s i)) at 1.
  unfold R.v56116, N.v56116.
  unfold R.v6, N.v6.
  rewrite ?node_56115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56117 (s : N.State) (i : N.Inputs) :
  R.v56117 (state s) (inputs i) = Zmod.unsigned (N.v56117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56117 s i)) at 1.
  unfold R.v56117, N.v56117.
  rewrite ?node_11678.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56118 (s : N.State) (i : N.Inputs) :
  R.v56118 (state s) (inputs i) = Zmod.unsigned (N.v56118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56118 s i)) at 1.
  unfold R.v56118, N.v56118.
  unfold R.v6, N.v6.
  rewrite ?node_11831.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56119 (s : N.State) (i : N.Inputs) :
  R.v56119 (state s) (inputs i) = Zmod.unsigned (N.v56119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56119 s i)) at 1.
  unfold R.v56119, N.v56119.
  rewrite ?node_56117.
  rewrite ?node_56118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56120 (s : N.State) (i : N.Inputs) :
  R.v56120 (state s) (inputs i) = Zmod.unsigned (N.v56120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56120 s i)) at 1.
  unfold R.v56120, N.v56120.
  rewrite ?node_56116.
  rewrite ?node_56119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56121 (s : N.State) (i : N.Inputs) :
  R.v56121 (state s) (inputs i) = Zmod.unsigned (N.v56121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56121 s i)) at 1.
  unfold R.v56121, N.v56121.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56122 (s : N.State) (i : N.Inputs) :
  R.v56122 (state s) (inputs i) = Zmod.unsigned (N.v56122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56122 s i)) at 1.
  unfold R.v56122, N.v56122.
  rewrite ?node_11685.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56123 (s : N.State) (i : N.Inputs) :
  R.v56123 (state s) (inputs i) = Zmod.unsigned (N.v56123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56123 s i)) at 1.
  unfold R.v56123, N.v56123.
  unfold R.v6, N.v6.
  rewrite ?node_11681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56124 (s : N.State) (i : N.Inputs) :
  R.v56124 (state s) (inputs i) = Zmod.unsigned (N.v56124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56124 s i)) at 1.
  unfold R.v56124, N.v56124.
  unfold R.v6, N.v6.
  rewrite ?node_11678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56125 (s : N.State) (i : N.Inputs) :
  R.v56125 (state s) (inputs i) = Zmod.unsigned (N.v56125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56125 s i)) at 1.
  unfold R.v56125, N.v56125.
  rewrite ?node_56123.
  rewrite ?node_56124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56126 (s : N.State) (i : N.Inputs) :
  R.v56126 (state s) (inputs i) = Zmod.unsigned (N.v56126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56126 s i)) at 1.
  unfold R.v56126, N.v56126.
  unfold R.v16484, N.v16484.
  rewrite ?node_56125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56127 (s : N.State) (i : N.Inputs) :
  R.v56127 (state s) (inputs i) = Zmod.unsigned (N.v56127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56127 s i)) at 1.
  unfold R.v56127, N.v56127.
  rewrite ?node_56122.
  rewrite ?node_56126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56128 (s : N.State) (i : N.Inputs) :
  R.v56128 (state s) (inputs i) = Zmod.unsigned (N.v56128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56128 s i)) at 1.
  unfold R.v56128, N.v56128.
  unfold R.v6, N.v6.
  rewrite ?node_56127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56129 (s : N.State) (i : N.Inputs) :
  R.v56129 (state s) (inputs i) = Zmod.unsigned (N.v56129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56129 s i)) at 1.
  unfold R.v56129, N.v56129.
  rewrite ?node_11686.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56130 (s : N.State) (i : N.Inputs) :
  R.v56130 (state s) (inputs i) = Zmod.unsigned (N.v56130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56130 s i)) at 1.
  unfold R.v56130, N.v56130.
  unfold R.v6, N.v6.
  rewrite ?node_11835.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56131 (s : N.State) (i : N.Inputs) :
  R.v56131 (state s) (inputs i) = Zmod.unsigned (N.v56131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56131 s i)) at 1.
  unfold R.v56131, N.v56131.
  rewrite ?node_56129.
  rewrite ?node_56130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56132 (s : N.State) (i : N.Inputs) :
  R.v56132 (state s) (inputs i) = Zmod.unsigned (N.v56132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56132 s i)) at 1.
  unfold R.v56132, N.v56132.
  rewrite ?node_56128.
  rewrite ?node_56131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56133 (s : N.State) (i : N.Inputs) :
  R.v56133 (state s) (inputs i) = Zmod.unsigned (N.v56133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56133 s i)) at 1.
  unfold R.v56133, N.v56133.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56134 (s : N.State) (i : N.Inputs) :
  R.v56134 (state s) (inputs i) = Zmod.unsigned (N.v56134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56134 s i)) at 1.
  unfold R.v56134, N.v56134.
  rewrite ?node_11831.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56135 (s : N.State) (i : N.Inputs) :
  R.v56135 (state s) (inputs i) = Zmod.unsigned (N.v56135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56135 s i)) at 1.
  unfold R.v56135, N.v56135.
  rewrite ?node_11827.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56136 (s : N.State) (i : N.Inputs) :
  R.v56136 (state s) (inputs i) = Zmod.unsigned (N.v56136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56136 s i)) at 1.
  unfold R.v56136, N.v56136.
  rewrite ?node_11823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56137 (s : N.State) (i : N.Inputs) :
  R.v56137 (state s) (inputs i) = Zmod.unsigned (N.v56137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56137 s i)) at 1.
  unfold R.v56137, N.v56137.
  unfold R.v6, N.v6.
  rewrite ?node_11819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56138 (s : N.State) (i : N.Inputs) :
  R.v56138 (state s) (inputs i) = Zmod.unsigned (N.v56138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56138 s i)) at 1.
  unfold R.v56138, N.v56138.
  unfold R.v6, N.v6.
  rewrite ?node_11800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56139 (s : N.State) (i : N.Inputs) :
  R.v56139 (state s) (inputs i) = Zmod.unsigned (N.v56139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56139 s i)) at 1.
  unfold R.v56139, N.v56139.
  rewrite ?node_56137.
  rewrite ?node_56138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56140 (s : N.State) (i : N.Inputs) :
  R.v56140 (state s) (inputs i) = Zmod.unsigned (N.v56140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56140 s i)) at 1.
  unfold R.v56140, N.v56140.
  unfold R.v16484, N.v16484.
  rewrite ?node_56139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56141 (s : N.State) (i : N.Inputs) :
  R.v56141 (state s) (inputs i) = Zmod.unsigned (N.v56141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56141 s i)) at 1.
  unfold R.v56141, N.v56141.
  rewrite ?node_56134.
  rewrite ?node_56135.
  rewrite ?node_56136.
  rewrite ?node_56140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56142 (s : N.State) (i : N.Inputs) :
  R.v56142 (state s) (inputs i) = Zmod.unsigned (N.v56142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56142 s i)) at 1.
  unfold R.v56142, N.v56142.
  unfold R.v6, N.v6.
  rewrite ?node_56141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56143 (s : N.State) (i : N.Inputs) :
  R.v56143 (state s) (inputs i) = Zmod.unsigned (N.v56143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56143 s i)) at 1.
  unfold R.v56143, N.v56143.
  rewrite ?node_11832.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56144 (s : N.State) (i : N.Inputs) :
  R.v56144 (state s) (inputs i) = Zmod.unsigned (N.v56144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56144 s i)) at 1.
  unfold R.v56144, N.v56144.
  unfold R.v6, N.v6.
  rewrite ?node_11975.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56145 (s : N.State) (i : N.Inputs) :
  R.v56145 (state s) (inputs i) = Zmod.unsigned (N.v56145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56145 s i)) at 1.
  unfold R.v56145, N.v56145.
  unfold R.v6, N.v6.
  rewrite ?node_11979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56146 (s : N.State) (i : N.Inputs) :
  R.v56146 (state s) (inputs i) = Zmod.unsigned (N.v56146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56146 s i)) at 1.
  unfold R.v56146, N.v56146.
  rewrite ?node_56143.
  rewrite ?node_56144.
  rewrite ?node_56145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56147 (s : N.State) (i : N.Inputs) :
  R.v56147 (state s) (inputs i) = Zmod.unsigned (N.v56147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56147 s i)) at 1.
  unfold R.v56147, N.v56147.
  rewrite ?node_56142.
  rewrite ?node_56146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56148 (s : N.State) (i : N.Inputs) :
  R.v56148 (state s) (inputs i) = Zmod.unsigned (N.v56148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56148 s i)) at 1.
  unfold R.v56148, N.v56148.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56149 (s : N.State) (i : N.Inputs) :
  R.v56149 (state s) (inputs i) = Zmod.unsigned (N.v56149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56149 s i)) at 1.
  unfold R.v56149, N.v56149.
  rewrite ?node_11823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56150 (s : N.State) (i : N.Inputs) :
  R.v56150 (state s) (inputs i) = Zmod.unsigned (N.v56150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56150 s i)) at 1.
  unfold R.v56150, N.v56150.
  unfold R.v6, N.v6.
  rewrite ?node_11819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56151 (s : N.State) (i : N.Inputs) :
  R.v56151 (state s) (inputs i) = Zmod.unsigned (N.v56151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56151 s i)) at 1.
  unfold R.v56151, N.v56151.
  unfold R.v6, N.v6.
  rewrite ?node_11800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56152 (s : N.State) (i : N.Inputs) :
  R.v56152 (state s) (inputs i) = Zmod.unsigned (N.v56152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56152 s i)) at 1.
  unfold R.v56152, N.v56152.
  rewrite ?node_56150.
  rewrite ?node_56151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56153 (s : N.State) (i : N.Inputs) :
  R.v56153 (state s) (inputs i) = Zmod.unsigned (N.v56153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56153 s i)) at 1.
  unfold R.v56153, N.v56153.
  unfold R.v16484, N.v16484.
  rewrite ?node_56152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56154 (s : N.State) (i : N.Inputs) :
  R.v56154 (state s) (inputs i) = Zmod.unsigned (N.v56154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56154 s i)) at 1.
  unfold R.v56154, N.v56154.
  rewrite ?node_56149.
  rewrite ?node_56153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56155 (s : N.State) (i : N.Inputs) :
  R.v56155 (state s) (inputs i) = Zmod.unsigned (N.v56155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56155 s i)) at 1.
  unfold R.v56155, N.v56155.
  unfold R.v6, N.v6.
  rewrite ?node_56154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56156 (s : N.State) (i : N.Inputs) :
  R.v56156 (state s) (inputs i) = Zmod.unsigned (N.v56156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56156 s i)) at 1.
  unfold R.v56156, N.v56156.
  rewrite ?node_11824.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56157 (s : N.State) (i : N.Inputs) :
  R.v56157 (state s) (inputs i) = Zmod.unsigned (N.v56157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56157 s i)) at 1.
  unfold R.v56157, N.v56157.
  unfold R.v6, N.v6.
  rewrite ?node_11975.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56158 (s : N.State) (i : N.Inputs) :
  R.v56158 (state s) (inputs i) = Zmod.unsigned (N.v56158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56158 s i)) at 1.
  unfold R.v56158, N.v56158.
  rewrite ?node_56156.
  rewrite ?node_56157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56159 (s : N.State) (i : N.Inputs) :
  R.v56159 (state s) (inputs i) = Zmod.unsigned (N.v56159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56159 s i)) at 1.
  unfold R.v56159, N.v56159.
  rewrite ?node_56155.
  rewrite ?node_56158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56160 (s : N.State) (i : N.Inputs) :
  R.v56160 (state s) (inputs i) = Zmod.unsigned (N.v56160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56160 s i)) at 1.
  unfold R.v56160, N.v56160.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56161 (s : N.State) (i : N.Inputs) :
  R.v56161 (state s) (inputs i) = Zmod.unsigned (N.v56161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56161 s i)) at 1.
  unfold R.v56161, N.v56161.
  rewrite ?node_11831.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56162 (s : N.State) (i : N.Inputs) :
  R.v56162 (state s) (inputs i) = Zmod.unsigned (N.v56162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56162 s i)) at 1.
  unfold R.v56162, N.v56162.
  unfold R.v6, N.v6.
  rewrite ?node_11827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56163 (s : N.State) (i : N.Inputs) :
  R.v56163 (state s) (inputs i) = Zmod.unsigned (N.v56163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56163 s i)) at 1.
  unfold R.v56163, N.v56163.
  unfold R.v6, N.v6.
  rewrite ?node_11824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56164 (s : N.State) (i : N.Inputs) :
  R.v56164 (state s) (inputs i) = Zmod.unsigned (N.v56164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56164 s i)) at 1.
  unfold R.v56164, N.v56164.
  rewrite ?node_56162.
  rewrite ?node_56163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56165 (s : N.State) (i : N.Inputs) :
  R.v56165 (state s) (inputs i) = Zmod.unsigned (N.v56165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56165 s i)) at 1.
  unfold R.v56165, N.v56165.
  unfold R.v16484, N.v16484.
  rewrite ?node_56164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56166 (s : N.State) (i : N.Inputs) :
  R.v56166 (state s) (inputs i) = Zmod.unsigned (N.v56166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56166 s i)) at 1.
  unfold R.v56166, N.v56166.
  rewrite ?node_56161.
  rewrite ?node_56165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56167 (s : N.State) (i : N.Inputs) :
  R.v56167 (state s) (inputs i) = Zmod.unsigned (N.v56167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56167 s i)) at 1.
  unfold R.v56167, N.v56167.
  unfold R.v6, N.v6.
  rewrite ?node_56166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56168 (s : N.State) (i : N.Inputs) :
  R.v56168 (state s) (inputs i) = Zmod.unsigned (N.v56168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56168 s i)) at 1.
  unfold R.v56168, N.v56168.
  rewrite ?node_11832.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56169 (s : N.State) (i : N.Inputs) :
  R.v56169 (state s) (inputs i) = Zmod.unsigned (N.v56169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56169 s i)) at 1.
  unfold R.v56169, N.v56169.
  unfold R.v6, N.v6.
  rewrite ?node_11979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56170 (s : N.State) (i : N.Inputs) :
  R.v56170 (state s) (inputs i) = Zmod.unsigned (N.v56170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56170 s i)) at 1.
  unfold R.v56170, N.v56170.
  rewrite ?node_56168.
  rewrite ?node_56169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56171 (s : N.State) (i : N.Inputs) :
  R.v56171 (state s) (inputs i) = Zmod.unsigned (N.v56171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56171 s i)) at 1.
  unfold R.v56171, N.v56171.
  rewrite ?node_56167.
  rewrite ?node_56170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56172 (s : N.State) (i : N.Inputs) :
  R.v56172 (state s) (inputs i) = Zmod.unsigned (N.v56172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56172 s i)) at 1.
  unfold R.v56172, N.v56172.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56173 (s : N.State) (i : N.Inputs) :
  R.v56173 (state s) (inputs i) = Zmod.unsigned (N.v56173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56173 s i)) at 1.
  unfold R.v56173, N.v56173.
  rewrite ?node_11975.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56174 (s : N.State) (i : N.Inputs) :
  R.v56174 (state s) (inputs i) = Zmod.unsigned (N.v56174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56174 s i)) at 1.
  unfold R.v56174, N.v56174.
  rewrite ?node_11971.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56175 (s : N.State) (i : N.Inputs) :
  R.v56175 (state s) (inputs i) = Zmod.unsigned (N.v56175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56175 s i)) at 1.
  unfold R.v56175, N.v56175.
  rewrite ?node_11967.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56176 (s : N.State) (i : N.Inputs) :
  R.v56176 (state s) (inputs i) = Zmod.unsigned (N.v56176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56176 s i)) at 1.
  unfold R.v56176, N.v56176.
  unfold R.v6, N.v6.
  rewrite ?node_11963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56177 (s : N.State) (i : N.Inputs) :
  R.v56177 (state s) (inputs i) = Zmod.unsigned (N.v56177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56177 s i)) at 1.
  unfold R.v56177, N.v56177.
  unfold R.v6, N.v6.
  rewrite ?node_11944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56178 (s : N.State) (i : N.Inputs) :
  R.v56178 (state s) (inputs i) = Zmod.unsigned (N.v56178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56178 s i)) at 1.
  unfold R.v56178, N.v56178.
  rewrite ?node_56176.
  rewrite ?node_56177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56179 (s : N.State) (i : N.Inputs) :
  R.v56179 (state s) (inputs i) = Zmod.unsigned (N.v56179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56179 s i)) at 1.
  unfold R.v56179, N.v56179.
  unfold R.v16484, N.v16484.
  rewrite ?node_56178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56180 (s : N.State) (i : N.Inputs) :
  R.v56180 (state s) (inputs i) = Zmod.unsigned (N.v56180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56180 s i)) at 1.
  unfold R.v56180, N.v56180.
  rewrite ?node_56173.
  rewrite ?node_56174.
  rewrite ?node_56175.
  rewrite ?node_56179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56181 (s : N.State) (i : N.Inputs) :
  R.v56181 (state s) (inputs i) = Zmod.unsigned (N.v56181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56181 s i)) at 1.
  unfold R.v56181, N.v56181.
  unfold R.v6, N.v6.
  rewrite ?node_56180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56182 (s : N.State) (i : N.Inputs) :
  R.v56182 (state s) (inputs i) = Zmod.unsigned (N.v56182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56182 s i)) at 1.
  unfold R.v56182, N.v56182.
  rewrite ?node_11976.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56183 (s : N.State) (i : N.Inputs) :
  R.v56183 (state s) (inputs i) = Zmod.unsigned (N.v56183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56183 s i)) at 1.
  unfold R.v56183, N.v56183.
  unfold R.v6, N.v6.
  rewrite ?node_12114.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56184 (s : N.State) (i : N.Inputs) :
  R.v56184 (state s) (inputs i) = Zmod.unsigned (N.v56184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56184 s i)) at 1.
  unfold R.v56184, N.v56184.
  unfold R.v6, N.v6.
  rewrite ?node_12122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56185 (s : N.State) (i : N.Inputs) :
  R.v56185 (state s) (inputs i) = Zmod.unsigned (N.v56185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56185 s i)) at 1.
  unfold R.v56185, N.v56185.
  rewrite ?node_56182.
  rewrite ?node_56183.
  rewrite ?node_56184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56186 (s : N.State) (i : N.Inputs) :
  R.v56186 (state s) (inputs i) = Zmod.unsigned (N.v56186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56186 s i)) at 1.
  unfold R.v56186, N.v56186.
  rewrite ?node_56181.
  rewrite ?node_56185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56187 (s : N.State) (i : N.Inputs) :
  R.v56187 (state s) (inputs i) = Zmod.unsigned (N.v56187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56187 s i)) at 1.
  unfold R.v56187, N.v56187.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56188 (s : N.State) (i : N.Inputs) :
  R.v56188 (state s) (inputs i) = Zmod.unsigned (N.v56188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56188 s i)) at 1.
  unfold R.v56188, N.v56188.
  rewrite ?node_11967.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56189 (s : N.State) (i : N.Inputs) :
  R.v56189 (state s) (inputs i) = Zmod.unsigned (N.v56189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56189 s i)) at 1.
  unfold R.v56189, N.v56189.
  unfold R.v6, N.v6.
  rewrite ?node_11963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56190 (s : N.State) (i : N.Inputs) :
  R.v56190 (state s) (inputs i) = Zmod.unsigned (N.v56190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56190 s i)) at 1.
  unfold R.v56190, N.v56190.
  unfold R.v6, N.v6.
  rewrite ?node_11944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56191 (s : N.State) (i : N.Inputs) :
  R.v56191 (state s) (inputs i) = Zmod.unsigned (N.v56191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56191 s i)) at 1.
  unfold R.v56191, N.v56191.
  rewrite ?node_56189.
  rewrite ?node_56190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56192 (s : N.State) (i : N.Inputs) :
  R.v56192 (state s) (inputs i) = Zmod.unsigned (N.v56192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56192 s i)) at 1.
  unfold R.v56192, N.v56192.
  unfold R.v16484, N.v16484.
  rewrite ?node_56191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56193 (s : N.State) (i : N.Inputs) :
  R.v56193 (state s) (inputs i) = Zmod.unsigned (N.v56193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56193 s i)) at 1.
  unfold R.v56193, N.v56193.
  rewrite ?node_56188.
  rewrite ?node_56192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56194 (s : N.State) (i : N.Inputs) :
  R.v56194 (state s) (inputs i) = Zmod.unsigned (N.v56194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56194 s i)) at 1.
  unfold R.v56194, N.v56194.
  unfold R.v6, N.v6.
  rewrite ?node_56193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56195 (s : N.State) (i : N.Inputs) :
  R.v56195 (state s) (inputs i) = Zmod.unsigned (N.v56195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56195 s i)) at 1.
  unfold R.v56195, N.v56195.
  rewrite ?node_11968.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56196 (s : N.State) (i : N.Inputs) :
  R.v56196 (state s) (inputs i) = Zmod.unsigned (N.v56196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56196 s i)) at 1.
  unfold R.v56196, N.v56196.
  unfold R.v6, N.v6.
  rewrite ?node_12114.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56197 (s : N.State) (i : N.Inputs) :
  R.v56197 (state s) (inputs i) = Zmod.unsigned (N.v56197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56197 s i)) at 1.
  unfold R.v56197, N.v56197.
  rewrite ?node_56195.
  rewrite ?node_56196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56198 (s : N.State) (i : N.Inputs) :
  R.v56198 (state s) (inputs i) = Zmod.unsigned (N.v56198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56198 s i)) at 1.
  unfold R.v56198, N.v56198.
  rewrite ?node_56194.
  rewrite ?node_56197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56199 (s : N.State) (i : N.Inputs) :
  R.v56199 (state s) (inputs i) = Zmod.unsigned (N.v56199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56199 s i)) at 1.
  unfold R.v56199, N.v56199.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56200 (s : N.State) (i : N.Inputs) :
  R.v56200 (state s) (inputs i) = Zmod.unsigned (N.v56200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56200 s i)) at 1.
  unfold R.v56200, N.v56200.
  rewrite ?node_11975.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56201 (s : N.State) (i : N.Inputs) :
  R.v56201 (state s) (inputs i) = Zmod.unsigned (N.v56201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56201 s i)) at 1.
  unfold R.v56201, N.v56201.
  unfold R.v6, N.v6.
  rewrite ?node_11971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56202 (s : N.State) (i : N.Inputs) :
  R.v56202 (state s) (inputs i) = Zmod.unsigned (N.v56202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56202 s i)) at 1.
  unfold R.v56202, N.v56202.
  unfold R.v6, N.v6.
  rewrite ?node_11968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56203 (s : N.State) (i : N.Inputs) :
  R.v56203 (state s) (inputs i) = Zmod.unsigned (N.v56203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56203 s i)) at 1.
  unfold R.v56203, N.v56203.
  rewrite ?node_56201.
  rewrite ?node_56202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56204 (s : N.State) (i : N.Inputs) :
  R.v56204 (state s) (inputs i) = Zmod.unsigned (N.v56204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56204 s i)) at 1.
  unfold R.v56204, N.v56204.
  unfold R.v16484, N.v16484.
  rewrite ?node_56203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56205 (s : N.State) (i : N.Inputs) :
  R.v56205 (state s) (inputs i) = Zmod.unsigned (N.v56205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56205 s i)) at 1.
  unfold R.v56205, N.v56205.
  rewrite ?node_56200.
  rewrite ?node_56204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56206 (s : N.State) (i : N.Inputs) :
  R.v56206 (state s) (inputs i) = Zmod.unsigned (N.v56206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56206 s i)) at 1.
  unfold R.v56206, N.v56206.
  unfold R.v6, N.v6.
  rewrite ?node_56205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56207 (s : N.State) (i : N.Inputs) :
  R.v56207 (state s) (inputs i) = Zmod.unsigned (N.v56207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56207 s i)) at 1.
  unfold R.v56207, N.v56207.
  rewrite ?node_11976.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56208 (s : N.State) (i : N.Inputs) :
  R.v56208 (state s) (inputs i) = Zmod.unsigned (N.v56208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56208 s i)) at 1.
  unfold R.v56208, N.v56208.
  unfold R.v6, N.v6.
  rewrite ?node_12122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56209 (s : N.State) (i : N.Inputs) :
  R.v56209 (state s) (inputs i) = Zmod.unsigned (N.v56209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56209 s i)) at 1.
  unfold R.v56209, N.v56209.
  rewrite ?node_56207.
  rewrite ?node_56208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56210 (s : N.State) (i : N.Inputs) :
  R.v56210 (state s) (inputs i) = Zmod.unsigned (N.v56210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56210 s i)) at 1.
  unfold R.v56210, N.v56210.
  rewrite ?node_56206.
  rewrite ?node_56209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56211 (s : N.State) (i : N.Inputs) :
  R.v56211 (state s) (inputs i) = Zmod.unsigned (N.v56211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56211 s i)) at 1.
  unfold R.v56211, N.v56211.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56212 (s : N.State) (i : N.Inputs) :
  R.v56212 (state s) (inputs i) = Zmod.unsigned (N.v56212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56212 s i)) at 1.
  unfold R.v56212, N.v56212.
  rewrite ?node_12114.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56213 (s : N.State) (i : N.Inputs) :
  R.v56213 (state s) (inputs i) = Zmod.unsigned (N.v56213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56213 s i)) at 1.
  unfold R.v56213, N.v56213.
  rewrite ?node_12110.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56214 (s : N.State) (i : N.Inputs) :
  R.v56214 (state s) (inputs i) = Zmod.unsigned (N.v56214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56214 s i)) at 1.
  unfold R.v56214, N.v56214.
  rewrite ?node_12106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56215 (s : N.State) (i : N.Inputs) :
  R.v56215 (state s) (inputs i) = Zmod.unsigned (N.v56215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56215 s i)) at 1.
  unfold R.v56215, N.v56215.
  unfold R.v6, N.v6.
  rewrite ?node_12102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56216 (s : N.State) (i : N.Inputs) :
  R.v56216 (state s) (inputs i) = Zmod.unsigned (N.v56216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56216 s i)) at 1.
  unfold R.v56216, N.v56216.
  unfold R.v6, N.v6.
  rewrite ?node_12083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56217 (s : N.State) (i : N.Inputs) :
  R.v56217 (state s) (inputs i) = Zmod.unsigned (N.v56217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56217 s i)) at 1.
  unfold R.v56217, N.v56217.
  rewrite ?node_56215.
  rewrite ?node_56216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56218 (s : N.State) (i : N.Inputs) :
  R.v56218 (state s) (inputs i) = Zmod.unsigned (N.v56218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56218 s i)) at 1.
  unfold R.v56218, N.v56218.
  unfold R.v16484, N.v16484.
  rewrite ?node_56217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56219 (s : N.State) (i : N.Inputs) :
  R.v56219 (state s) (inputs i) = Zmod.unsigned (N.v56219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56219 s i)) at 1.
  unfold R.v56219, N.v56219.
  rewrite ?node_56212.
  rewrite ?node_56213.
  rewrite ?node_56214.
  rewrite ?node_56218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56220 (s : N.State) (i : N.Inputs) :
  R.v56220 (state s) (inputs i) = Zmod.unsigned (N.v56220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56220 s i)) at 1.
  unfold R.v56220, N.v56220.
  unfold R.v6, N.v6.
  rewrite ?node_56219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56221 (s : N.State) (i : N.Inputs) :
  R.v56221 (state s) (inputs i) = Zmod.unsigned (N.v56221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56221 s i)) at 1.
  unfold R.v56221, N.v56221.
  rewrite ?node_12115.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56222 (s : N.State) (i : N.Inputs) :
  R.v56222 (state s) (inputs i) = Zmod.unsigned (N.v56222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56222 s i)) at 1.
  unfold R.v56222, N.v56222.
  unfold R.v6, N.v6.
  rewrite ?node_12255.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56223 (s : N.State) (i : N.Inputs) :
  R.v56223 (state s) (inputs i) = Zmod.unsigned (N.v56223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56223 s i)) at 1.
  unfold R.v56223, N.v56223.
  unfold R.v6, N.v6.
  rewrite ?node_12259.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56224 (s : N.State) (i : N.Inputs) :
  R.v56224 (state s) (inputs i) = Zmod.unsigned (N.v56224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56224 s i)) at 1.
  unfold R.v56224, N.v56224.
  rewrite ?node_56221.
  rewrite ?node_56222.
  rewrite ?node_56223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56225 (s : N.State) (i : N.Inputs) :
  R.v56225 (state s) (inputs i) = Zmod.unsigned (N.v56225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56225 s i)) at 1.
  unfold R.v56225, N.v56225.
  rewrite ?node_56220.
  rewrite ?node_56224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56226 (s : N.State) (i : N.Inputs) :
  R.v56226 (state s) (inputs i) = Zmod.unsigned (N.v56226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56226 s i)) at 1.
  unfold R.v56226, N.v56226.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56227 (s : N.State) (i : N.Inputs) :
  R.v56227 (state s) (inputs i) = Zmod.unsigned (N.v56227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56227 s i)) at 1.
  unfold R.v56227, N.v56227.
  rewrite ?node_12106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56228 (s : N.State) (i : N.Inputs) :
  R.v56228 (state s) (inputs i) = Zmod.unsigned (N.v56228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56228 s i)) at 1.
  unfold R.v56228, N.v56228.
  unfold R.v6, N.v6.
  rewrite ?node_12102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56229 (s : N.State) (i : N.Inputs) :
  R.v56229 (state s) (inputs i) = Zmod.unsigned (N.v56229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56229 s i)) at 1.
  unfold R.v56229, N.v56229.
  unfold R.v6, N.v6.
  rewrite ?node_12083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56230 (s : N.State) (i : N.Inputs) :
  R.v56230 (state s) (inputs i) = Zmod.unsigned (N.v56230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56230 s i)) at 1.
  unfold R.v56230, N.v56230.
  rewrite ?node_56228.
  rewrite ?node_56229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56231 (s : N.State) (i : N.Inputs) :
  R.v56231 (state s) (inputs i) = Zmod.unsigned (N.v56231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56231 s i)) at 1.
  unfold R.v56231, N.v56231.
  unfold R.v16484, N.v16484.
  rewrite ?node_56230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56232 (s : N.State) (i : N.Inputs) :
  R.v56232 (state s) (inputs i) = Zmod.unsigned (N.v56232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56232 s i)) at 1.
  unfold R.v56232, N.v56232.
  rewrite ?node_56227.
  rewrite ?node_56231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56233 (s : N.State) (i : N.Inputs) :
  R.v56233 (state s) (inputs i) = Zmod.unsigned (N.v56233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56233 s i)) at 1.
  unfold R.v56233, N.v56233.
  unfold R.v6, N.v6.
  rewrite ?node_56232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56234 (s : N.State) (i : N.Inputs) :
  R.v56234 (state s) (inputs i) = Zmod.unsigned (N.v56234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56234 s i)) at 1.
  unfold R.v56234, N.v56234.
  rewrite ?node_12107.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56235 (s : N.State) (i : N.Inputs) :
  R.v56235 (state s) (inputs i) = Zmod.unsigned (N.v56235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56235 s i)) at 1.
  unfold R.v56235, N.v56235.
  unfold R.v6, N.v6.
  rewrite ?node_12255.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56236 (s : N.State) (i : N.Inputs) :
  R.v56236 (state s) (inputs i) = Zmod.unsigned (N.v56236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56236 s i)) at 1.
  unfold R.v56236, N.v56236.
  rewrite ?node_56234.
  rewrite ?node_56235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56237 (s : N.State) (i : N.Inputs) :
  R.v56237 (state s) (inputs i) = Zmod.unsigned (N.v56237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56237 s i)) at 1.
  unfold R.v56237, N.v56237.
  rewrite ?node_56233.
  rewrite ?node_56236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56238 (s : N.State) (i : N.Inputs) :
  R.v56238 (state s) (inputs i) = Zmod.unsigned (N.v56238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56238 s i)) at 1.
  unfold R.v56238, N.v56238.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56239 (s : N.State) (i : N.Inputs) :
  R.v56239 (state s) (inputs i) = Zmod.unsigned (N.v56239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56239 s i)) at 1.
  unfold R.v56239, N.v56239.
  rewrite ?node_12114.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56240 (s : N.State) (i : N.Inputs) :
  R.v56240 (state s) (inputs i) = Zmod.unsigned (N.v56240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56240 s i)) at 1.
  unfold R.v56240, N.v56240.
  unfold R.v6, N.v6.
  rewrite ?node_12110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56241 (s : N.State) (i : N.Inputs) :
  R.v56241 (state s) (inputs i) = Zmod.unsigned (N.v56241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56241 s i)) at 1.
  unfold R.v56241, N.v56241.
  unfold R.v6, N.v6.
  rewrite ?node_12107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56242 (s : N.State) (i : N.Inputs) :
  R.v56242 (state s) (inputs i) = Zmod.unsigned (N.v56242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56242 s i)) at 1.
  unfold R.v56242, N.v56242.
  rewrite ?node_56240.
  rewrite ?node_56241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56243 (s : N.State) (i : N.Inputs) :
  R.v56243 (state s) (inputs i) = Zmod.unsigned (N.v56243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56243 s i)) at 1.
  unfold R.v56243, N.v56243.
  unfold R.v16484, N.v16484.
  rewrite ?node_56242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56244 (s : N.State) (i : N.Inputs) :
  R.v56244 (state s) (inputs i) = Zmod.unsigned (N.v56244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56244 s i)) at 1.
  unfold R.v56244, N.v56244.
  rewrite ?node_56239.
  rewrite ?node_56243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56245 (s : N.State) (i : N.Inputs) :
  R.v56245 (state s) (inputs i) = Zmod.unsigned (N.v56245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56245 s i)) at 1.
  unfold R.v56245, N.v56245.
  unfold R.v6, N.v6.
  rewrite ?node_56244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56246 (s : N.State) (i : N.Inputs) :
  R.v56246 (state s) (inputs i) = Zmod.unsigned (N.v56246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56246 s i)) at 1.
  unfold R.v56246, N.v56246.
  rewrite ?node_12115.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56247 (s : N.State) (i : N.Inputs) :
  R.v56247 (state s) (inputs i) = Zmod.unsigned (N.v56247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56247 s i)) at 1.
  unfold R.v56247, N.v56247.
  unfold R.v6, N.v6.
  rewrite ?node_12259.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56248 (s : N.State) (i : N.Inputs) :
  R.v56248 (state s) (inputs i) = Zmod.unsigned (N.v56248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56248 s i)) at 1.
  unfold R.v56248, N.v56248.
  rewrite ?node_56246.
  rewrite ?node_56247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56249 (s : N.State) (i : N.Inputs) :
  R.v56249 (state s) (inputs i) = Zmod.unsigned (N.v56249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56249 s i)) at 1.
  unfold R.v56249, N.v56249.
  rewrite ?node_56245.
  rewrite ?node_56248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56250 (s : N.State) (i : N.Inputs) :
  R.v56250 (state s) (inputs i) = Zmod.unsigned (N.v56250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56250 s i)) at 1.
  unfold R.v56250, N.v56250.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56251 (s : N.State) (i : N.Inputs) :
  R.v56251 (state s) (inputs i) = Zmod.unsigned (N.v56251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56251 s i)) at 1.
  unfold R.v56251, N.v56251.
  rewrite ?node_12255.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56252 (s : N.State) (i : N.Inputs) :
  R.v56252 (state s) (inputs i) = Zmod.unsigned (N.v56252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56252 s i)) at 1.
  unfold R.v56252, N.v56252.
  rewrite ?node_12251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56253 (s : N.State) (i : N.Inputs) :
  R.v56253 (state s) (inputs i) = Zmod.unsigned (N.v56253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56253 s i)) at 1.
  unfold R.v56253, N.v56253.
  rewrite ?node_12247.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56254 (s : N.State) (i : N.Inputs) :
  R.v56254 (state s) (inputs i) = Zmod.unsigned (N.v56254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56254 s i)) at 1.
  unfold R.v56254, N.v56254.
  unfold R.v6, N.v6.
  rewrite ?node_12243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56255 (s : N.State) (i : N.Inputs) :
  R.v56255 (state s) (inputs i) = Zmod.unsigned (N.v56255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56255 s i)) at 1.
  unfold R.v56255, N.v56255.
  unfold R.v6, N.v6.
  rewrite ?node_12224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56256 (s : N.State) (i : N.Inputs) :
  R.v56256 (state s) (inputs i) = Zmod.unsigned (N.v56256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56256 s i)) at 1.
  unfold R.v56256, N.v56256.
  rewrite ?node_56254.
  rewrite ?node_56255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56257 (s : N.State) (i : N.Inputs) :
  R.v56257 (state s) (inputs i) = Zmod.unsigned (N.v56257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56257 s i)) at 1.
  unfold R.v56257, N.v56257.
  unfold R.v16484, N.v16484.
  rewrite ?node_56256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56258 (s : N.State) (i : N.Inputs) :
  R.v56258 (state s) (inputs i) = Zmod.unsigned (N.v56258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56258 s i)) at 1.
  unfold R.v56258, N.v56258.
  rewrite ?node_56251.
  rewrite ?node_56252.
  rewrite ?node_56253.
  rewrite ?node_56257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56259 (s : N.State) (i : N.Inputs) :
  R.v56259 (state s) (inputs i) = Zmod.unsigned (N.v56259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56259 s i)) at 1.
  unfold R.v56259, N.v56259.
  unfold R.v6, N.v6.
  rewrite ?node_56258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56260 (s : N.State) (i : N.Inputs) :
  R.v56260 (state s) (inputs i) = Zmod.unsigned (N.v56260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56260 s i)) at 1.
  unfold R.v56260, N.v56260.
  rewrite ?node_12256.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56261 (s : N.State) (i : N.Inputs) :
  R.v56261 (state s) (inputs i) = Zmod.unsigned (N.v56261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56261 s i)) at 1.
  unfold R.v56261, N.v56261.
  unfold R.v6, N.v6.
  rewrite ?node_12393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56262 (s : N.State) (i : N.Inputs) :
  R.v56262 (state s) (inputs i) = Zmod.unsigned (N.v56262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56262 s i)) at 1.
  unfold R.v56262, N.v56262.
  unfold R.v6, N.v6.
  rewrite ?node_12397.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56263 (s : N.State) (i : N.Inputs) :
  R.v56263 (state s) (inputs i) = Zmod.unsigned (N.v56263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56263 s i)) at 1.
  unfold R.v56263, N.v56263.
  rewrite ?node_56260.
  rewrite ?node_56261.
  rewrite ?node_56262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56264 (s : N.State) (i : N.Inputs) :
  R.v56264 (state s) (inputs i) = Zmod.unsigned (N.v56264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56264 s i)) at 1.
  unfold R.v56264, N.v56264.
  rewrite ?node_56259.
  rewrite ?node_56263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56265 (s : N.State) (i : N.Inputs) :
  R.v56265 (state s) (inputs i) = Zmod.unsigned (N.v56265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56265 s i)) at 1.
  unfold R.v56265, N.v56265.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56266 (s : N.State) (i : N.Inputs) :
  R.v56266 (state s) (inputs i) = Zmod.unsigned (N.v56266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56266 s i)) at 1.
  unfold R.v56266, N.v56266.
  rewrite ?node_12247.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56267 (s : N.State) (i : N.Inputs) :
  R.v56267 (state s) (inputs i) = Zmod.unsigned (N.v56267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56267 s i)) at 1.
  unfold R.v56267, N.v56267.
  unfold R.v6, N.v6.
  rewrite ?node_12243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56268 (s : N.State) (i : N.Inputs) :
  R.v56268 (state s) (inputs i) = Zmod.unsigned (N.v56268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56268 s i)) at 1.
  unfold R.v56268, N.v56268.
  unfold R.v6, N.v6.
  rewrite ?node_12224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56269 (s : N.State) (i : N.Inputs) :
  R.v56269 (state s) (inputs i) = Zmod.unsigned (N.v56269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56269 s i)) at 1.
  unfold R.v56269, N.v56269.
  rewrite ?node_56267.
  rewrite ?node_56268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56270 (s : N.State) (i : N.Inputs) :
  R.v56270 (state s) (inputs i) = Zmod.unsigned (N.v56270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56270 s i)) at 1.
  unfold R.v56270, N.v56270.
  unfold R.v16484, N.v16484.
  rewrite ?node_56269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56271 (s : N.State) (i : N.Inputs) :
  R.v56271 (state s) (inputs i) = Zmod.unsigned (N.v56271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56271 s i)) at 1.
  unfold R.v56271, N.v56271.
  rewrite ?node_56266.
  rewrite ?node_56270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56272 (s : N.State) (i : N.Inputs) :
  R.v56272 (state s) (inputs i) = Zmod.unsigned (N.v56272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56272 s i)) at 1.
  unfold R.v56272, N.v56272.
  unfold R.v6, N.v6.
  rewrite ?node_56271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56273 (s : N.State) (i : N.Inputs) :
  R.v56273 (state s) (inputs i) = Zmod.unsigned (N.v56273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56273 s i)) at 1.
  unfold R.v56273, N.v56273.
  rewrite ?node_12248.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56274 (s : N.State) (i : N.Inputs) :
  R.v56274 (state s) (inputs i) = Zmod.unsigned (N.v56274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56274 s i)) at 1.
  unfold R.v56274, N.v56274.
  unfold R.v6, N.v6.
  rewrite ?node_12393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56275 (s : N.State) (i : N.Inputs) :
  R.v56275 (state s) (inputs i) = Zmod.unsigned (N.v56275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56275 s i)) at 1.
  unfold R.v56275, N.v56275.
  rewrite ?node_56273.
  rewrite ?node_56274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56276 (s : N.State) (i : N.Inputs) :
  R.v56276 (state s) (inputs i) = Zmod.unsigned (N.v56276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56276 s i)) at 1.
  unfold R.v56276, N.v56276.
  rewrite ?node_56272.
  rewrite ?node_56275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56277 (s : N.State) (i : N.Inputs) :
  R.v56277 (state s) (inputs i) = Zmod.unsigned (N.v56277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56277 s i)) at 1.
  unfold R.v56277, N.v56277.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56278 (s : N.State) (i : N.Inputs) :
  R.v56278 (state s) (inputs i) = Zmod.unsigned (N.v56278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56278 s i)) at 1.
  unfold R.v56278, N.v56278.
  rewrite ?node_12255.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56279 (s : N.State) (i : N.Inputs) :
  R.v56279 (state s) (inputs i) = Zmod.unsigned (N.v56279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56279 s i)) at 1.
  unfold R.v56279, N.v56279.
  unfold R.v6, N.v6.
  rewrite ?node_12251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56280 (s : N.State) (i : N.Inputs) :
  R.v56280 (state s) (inputs i) = Zmod.unsigned (N.v56280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56280 s i)) at 1.
  unfold R.v56280, N.v56280.
  unfold R.v6, N.v6.
  rewrite ?node_12248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56281 (s : N.State) (i : N.Inputs) :
  R.v56281 (state s) (inputs i) = Zmod.unsigned (N.v56281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56281 s i)) at 1.
  unfold R.v56281, N.v56281.
  rewrite ?node_56279.
  rewrite ?node_56280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56282 (s : N.State) (i : N.Inputs) :
  R.v56282 (state s) (inputs i) = Zmod.unsigned (N.v56282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56282 s i)) at 1.
  unfold R.v56282, N.v56282.
  unfold R.v16484, N.v16484.
  rewrite ?node_56281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56283 (s : N.State) (i : N.Inputs) :
  R.v56283 (state s) (inputs i) = Zmod.unsigned (N.v56283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56283 s i)) at 1.
  unfold R.v56283, N.v56283.
  rewrite ?node_56278.
  rewrite ?node_56282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56284 (s : N.State) (i : N.Inputs) :
  R.v56284 (state s) (inputs i) = Zmod.unsigned (N.v56284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56284 s i)) at 1.
  unfold R.v56284, N.v56284.
  unfold R.v6, N.v6.
  rewrite ?node_56283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56285 (s : N.State) (i : N.Inputs) :
  R.v56285 (state s) (inputs i) = Zmod.unsigned (N.v56285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56285 s i)) at 1.
  unfold R.v56285, N.v56285.
  rewrite ?node_12256.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56286 (s : N.State) (i : N.Inputs) :
  R.v56286 (state s) (inputs i) = Zmod.unsigned (N.v56286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56286 s i)) at 1.
  unfold R.v56286, N.v56286.
  unfold R.v6, N.v6.
  rewrite ?node_12397.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56287 (s : N.State) (i : N.Inputs) :
  R.v56287 (state s) (inputs i) = Zmod.unsigned (N.v56287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56287 s i)) at 1.
  unfold R.v56287, N.v56287.
  rewrite ?node_56285.
  rewrite ?node_56286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56288 (s : N.State) (i : N.Inputs) :
  R.v56288 (state s) (inputs i) = Zmod.unsigned (N.v56288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56288 s i)) at 1.
  unfold R.v56288, N.v56288.
  rewrite ?node_56284.
  rewrite ?node_56287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56289 (s : N.State) (i : N.Inputs) :
  R.v56289 (state s) (inputs i) = Zmod.unsigned (N.v56289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56289 s i)) at 1.
  unfold R.v56289, N.v56289.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56290 (s : N.State) (i : N.Inputs) :
  R.v56290 (state s) (inputs i) = Zmod.unsigned (N.v56290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56290 s i)) at 1.
  unfold R.v56290, N.v56290.
  rewrite ?node_12393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56291 (s : N.State) (i : N.Inputs) :
  R.v56291 (state s) (inputs i) = Zmod.unsigned (N.v56291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56291 s i)) at 1.
  unfold R.v56291, N.v56291.
  rewrite ?node_12389.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56292 (s : N.State) (i : N.Inputs) :
  R.v56292 (state s) (inputs i) = Zmod.unsigned (N.v56292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56292 s i)) at 1.
  unfold R.v56292, N.v56292.
  rewrite ?node_12385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56293 (s : N.State) (i : N.Inputs) :
  R.v56293 (state s) (inputs i) = Zmod.unsigned (N.v56293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56293 s i)) at 1.
  unfold R.v56293, N.v56293.
  unfold R.v6, N.v6.
  rewrite ?node_12381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56294 (s : N.State) (i : N.Inputs) :
  R.v56294 (state s) (inputs i) = Zmod.unsigned (N.v56294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56294 s i)) at 1.
  unfold R.v56294, N.v56294.
  unfold R.v6, N.v6.
  rewrite ?node_12364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56295 (s : N.State) (i : N.Inputs) :
  R.v56295 (state s) (inputs i) = Zmod.unsigned (N.v56295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56295 s i)) at 1.
  unfold R.v56295, N.v56295.
  rewrite ?node_56293.
  rewrite ?node_56294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56296 (s : N.State) (i : N.Inputs) :
  R.v56296 (state s) (inputs i) = Zmod.unsigned (N.v56296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56296 s i)) at 1.
  unfold R.v56296, N.v56296.
  unfold R.v16484, N.v16484.
  rewrite ?node_56295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56297 (s : N.State) (i : N.Inputs) :
  R.v56297 (state s) (inputs i) = Zmod.unsigned (N.v56297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56297 s i)) at 1.
  unfold R.v56297, N.v56297.
  rewrite ?node_56290.
  rewrite ?node_56291.
  rewrite ?node_56292.
  rewrite ?node_56296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56298 (s : N.State) (i : N.Inputs) :
  R.v56298 (state s) (inputs i) = Zmod.unsigned (N.v56298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56298 s i)) at 1.
  unfold R.v56298, N.v56298.
  unfold R.v6, N.v6.
  rewrite ?node_56297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56299 (s : N.State) (i : N.Inputs) :
  R.v56299 (state s) (inputs i) = Zmod.unsigned (N.v56299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56299 s i)) at 1.
  unfold R.v56299, N.v56299.
  rewrite ?node_12394.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56300 (s : N.State) (i : N.Inputs) :
  R.v56300 (state s) (inputs i) = Zmod.unsigned (N.v56300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56300 s i)) at 1.
  unfold R.v56300, N.v56300.
  unfold R.v6, N.v6.
  rewrite ?node_12527.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56301 (s : N.State) (i : N.Inputs) :
  R.v56301 (state s) (inputs i) = Zmod.unsigned (N.v56301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56301 s i)) at 1.
  unfold R.v56301, N.v56301.
  unfold R.v6, N.v6.
  rewrite ?node_12531.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56302 (s : N.State) (i : N.Inputs) :
  R.v56302 (state s) (inputs i) = Zmod.unsigned (N.v56302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56302 s i)) at 1.
  unfold R.v56302, N.v56302.
  rewrite ?node_56299.
  rewrite ?node_56300.
  rewrite ?node_56301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56303 (s : N.State) (i : N.Inputs) :
  R.v56303 (state s) (inputs i) = Zmod.unsigned (N.v56303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56303 s i)) at 1.
  unfold R.v56303, N.v56303.
  rewrite ?node_56298.
  rewrite ?node_56302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56304 (s : N.State) (i : N.Inputs) :
  R.v56304 (state s) (inputs i) = Zmod.unsigned (N.v56304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56304 s i)) at 1.
  unfold R.v56304, N.v56304.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56305 (s : N.State) (i : N.Inputs) :
  R.v56305 (state s) (inputs i) = Zmod.unsigned (N.v56305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56305 s i)) at 1.
  unfold R.v56305, N.v56305.
  rewrite ?node_12385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56306 (s : N.State) (i : N.Inputs) :
  R.v56306 (state s) (inputs i) = Zmod.unsigned (N.v56306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56306 s i)) at 1.
  unfold R.v56306, N.v56306.
  unfold R.v6, N.v6.
  rewrite ?node_12381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56307 (s : N.State) (i : N.Inputs) :
  R.v56307 (state s) (inputs i) = Zmod.unsigned (N.v56307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56307 s i)) at 1.
  unfold R.v56307, N.v56307.
  unfold R.v6, N.v6.
  rewrite ?node_12364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56308 (s : N.State) (i : N.Inputs) :
  R.v56308 (state s) (inputs i) = Zmod.unsigned (N.v56308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56308 s i)) at 1.
  unfold R.v56308, N.v56308.
  rewrite ?node_56306.
  rewrite ?node_56307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56309 (s : N.State) (i : N.Inputs) :
  R.v56309 (state s) (inputs i) = Zmod.unsigned (N.v56309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56309 s i)) at 1.
  unfold R.v56309, N.v56309.
  unfold R.v16484, N.v16484.
  rewrite ?node_56308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56310 (s : N.State) (i : N.Inputs) :
  R.v56310 (state s) (inputs i) = Zmod.unsigned (N.v56310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56310 s i)) at 1.
  unfold R.v56310, N.v56310.
  rewrite ?node_56305.
  rewrite ?node_56309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56311 (s : N.State) (i : N.Inputs) :
  R.v56311 (state s) (inputs i) = Zmod.unsigned (N.v56311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56311 s i)) at 1.
  unfold R.v56311, N.v56311.
  unfold R.v6, N.v6.
  rewrite ?node_56310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56312 (s : N.State) (i : N.Inputs) :
  R.v56312 (state s) (inputs i) = Zmod.unsigned (N.v56312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56312 s i)) at 1.
  unfold R.v56312, N.v56312.
  rewrite ?node_12386.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56313 (s : N.State) (i : N.Inputs) :
  R.v56313 (state s) (inputs i) = Zmod.unsigned (N.v56313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56313 s i)) at 1.
  unfold R.v56313, N.v56313.
  unfold R.v6, N.v6.
  rewrite ?node_12527.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56314 (s : N.State) (i : N.Inputs) :
  R.v56314 (state s) (inputs i) = Zmod.unsigned (N.v56314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56314 s i)) at 1.
  unfold R.v56314, N.v56314.
  rewrite ?node_56312.
  rewrite ?node_56313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56315 (s : N.State) (i : N.Inputs) :
  R.v56315 (state s) (inputs i) = Zmod.unsigned (N.v56315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56315 s i)) at 1.
  unfold R.v56315, N.v56315.
  rewrite ?node_56311.
  rewrite ?node_56314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56316 (s : N.State) (i : N.Inputs) :
  R.v56316 (state s) (inputs i) = Zmod.unsigned (N.v56316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56316 s i)) at 1.
  unfold R.v56316, N.v56316.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56317 (s : N.State) (i : N.Inputs) :
  R.v56317 (state s) (inputs i) = Zmod.unsigned (N.v56317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56317 s i)) at 1.
  unfold R.v56317, N.v56317.
  rewrite ?node_12393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56318 (s : N.State) (i : N.Inputs) :
  R.v56318 (state s) (inputs i) = Zmod.unsigned (N.v56318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56318 s i)) at 1.
  unfold R.v56318, N.v56318.
  unfold R.v6, N.v6.
  rewrite ?node_12389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56319 (s : N.State) (i : N.Inputs) :
  R.v56319 (state s) (inputs i) = Zmod.unsigned (N.v56319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56319 s i)) at 1.
  unfold R.v56319, N.v56319.
  unfold R.v6, N.v6.
  rewrite ?node_12386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56320 (s : N.State) (i : N.Inputs) :
  R.v56320 (state s) (inputs i) = Zmod.unsigned (N.v56320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56320 s i)) at 1.
  unfold R.v56320, N.v56320.
  rewrite ?node_56318.
  rewrite ?node_56319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56321 (s : N.State) (i : N.Inputs) :
  R.v56321 (state s) (inputs i) = Zmod.unsigned (N.v56321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56321 s i)) at 1.
  unfold R.v56321, N.v56321.
  unfold R.v16484, N.v16484.
  rewrite ?node_56320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56322 (s : N.State) (i : N.Inputs) :
  R.v56322 (state s) (inputs i) = Zmod.unsigned (N.v56322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56322 s i)) at 1.
  unfold R.v56322, N.v56322.
  rewrite ?node_56317.
  rewrite ?node_56321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56323 (s : N.State) (i : N.Inputs) :
  R.v56323 (state s) (inputs i) = Zmod.unsigned (N.v56323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56323 s i)) at 1.
  unfold R.v56323, N.v56323.
  unfold R.v6, N.v6.
  rewrite ?node_56322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56324 (s : N.State) (i : N.Inputs) :
  R.v56324 (state s) (inputs i) = Zmod.unsigned (N.v56324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56324 s i)) at 1.
  unfold R.v56324, N.v56324.
  rewrite ?node_12394.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56325 (s : N.State) (i : N.Inputs) :
  R.v56325 (state s) (inputs i) = Zmod.unsigned (N.v56325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56325 s i)) at 1.
  unfold R.v56325, N.v56325.
  unfold R.v6, N.v6.
  rewrite ?node_12531.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56326 (s : N.State) (i : N.Inputs) :
  R.v56326 (state s) (inputs i) = Zmod.unsigned (N.v56326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56326 s i)) at 1.
  unfold R.v56326, N.v56326.
  rewrite ?node_56324.
  rewrite ?node_56325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56327 (s : N.State) (i : N.Inputs) :
  R.v56327 (state s) (inputs i) = Zmod.unsigned (N.v56327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56327 s i)) at 1.
  unfold R.v56327, N.v56327.
  rewrite ?node_56323.
  rewrite ?node_56326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56328 (s : N.State) (i : N.Inputs) :
  R.v56328 (state s) (inputs i) = Zmod.unsigned (N.v56328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56328 s i)) at 1.
  unfold R.v56328, N.v56328.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56329 (s : N.State) (i : N.Inputs) :
  R.v56329 (state s) (inputs i) = Zmod.unsigned (N.v56329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56329 s i)) at 1.
  unfold R.v56329, N.v56329.
  rewrite ?node_12527.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56330 (s : N.State) (i : N.Inputs) :
  R.v56330 (state s) (inputs i) = Zmod.unsigned (N.v56330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56330 s i)) at 1.
  unfold R.v56330, N.v56330.
  rewrite ?node_12523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56331 (s : N.State) (i : N.Inputs) :
  R.v56331 (state s) (inputs i) = Zmod.unsigned (N.v56331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56331 s i)) at 1.
  unfold R.v56331, N.v56331.
  rewrite ?node_12519.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56332 (s : N.State) (i : N.Inputs) :
  R.v56332 (state s) (inputs i) = Zmod.unsigned (N.v56332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56332 s i)) at 1.
  unfold R.v56332, N.v56332.
  unfold R.v6, N.v6.
  rewrite ?node_12515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56333 (s : N.State) (i : N.Inputs) :
  R.v56333 (state s) (inputs i) = Zmod.unsigned (N.v56333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56333 s i)) at 1.
  unfold R.v56333, N.v56333.
  unfold R.v6, N.v6.
  rewrite ?node_12498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56334 (s : N.State) (i : N.Inputs) :
  R.v56334 (state s) (inputs i) = Zmod.unsigned (N.v56334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56334 s i)) at 1.
  unfold R.v56334, N.v56334.
  rewrite ?node_56332.
  rewrite ?node_56333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56335 (s : N.State) (i : N.Inputs) :
  R.v56335 (state s) (inputs i) = Zmod.unsigned (N.v56335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56335 s i)) at 1.
  unfold R.v56335, N.v56335.
  unfold R.v16484, N.v16484.
  rewrite ?node_56334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56336 (s : N.State) (i : N.Inputs) :
  R.v56336 (state s) (inputs i) = Zmod.unsigned (N.v56336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56336 s i)) at 1.
  unfold R.v56336, N.v56336.
  rewrite ?node_56329.
  rewrite ?node_56330.
  rewrite ?node_56331.
  rewrite ?node_56335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56337 (s : N.State) (i : N.Inputs) :
  R.v56337 (state s) (inputs i) = Zmod.unsigned (N.v56337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56337 s i)) at 1.
  unfold R.v56337, N.v56337.
  unfold R.v6, N.v6.
  rewrite ?node_56336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56338 (s : N.State) (i : N.Inputs) :
  R.v56338 (state s) (inputs i) = Zmod.unsigned (N.v56338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56338 s i)) at 1.
  unfold R.v56338, N.v56338.
  rewrite ?node_12528.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56339 (s : N.State) (i : N.Inputs) :
  R.v56339 (state s) (inputs i) = Zmod.unsigned (N.v56339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56339 s i)) at 1.
  unfold R.v56339, N.v56339.
  unfold R.v6, N.v6.
  rewrite ?node_12660.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56340 (s : N.State) (i : N.Inputs) :
  R.v56340 (state s) (inputs i) = Zmod.unsigned (N.v56340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56340 s i)) at 1.
  unfold R.v56340, N.v56340.
  unfold R.v6, N.v6.
  rewrite ?node_12664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56341 (s : N.State) (i : N.Inputs) :
  R.v56341 (state s) (inputs i) = Zmod.unsigned (N.v56341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56341 s i)) at 1.
  unfold R.v56341, N.v56341.
  rewrite ?node_56338.
  rewrite ?node_56339.
  rewrite ?node_56340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56342 (s : N.State) (i : N.Inputs) :
  R.v56342 (state s) (inputs i) = Zmod.unsigned (N.v56342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56342 s i)) at 1.
  unfold R.v56342, N.v56342.
  rewrite ?node_56337.
  rewrite ?node_56341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56343 (s : N.State) (i : N.Inputs) :
  R.v56343 (state s) (inputs i) = Zmod.unsigned (N.v56343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56343 s i)) at 1.
  unfold R.v56343, N.v56343.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56344 (s : N.State) (i : N.Inputs) :
  R.v56344 (state s) (inputs i) = Zmod.unsigned (N.v56344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56344 s i)) at 1.
  unfold R.v56344, N.v56344.
  rewrite ?node_12519.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56345 (s : N.State) (i : N.Inputs) :
  R.v56345 (state s) (inputs i) = Zmod.unsigned (N.v56345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56345 s i)) at 1.
  unfold R.v56345, N.v56345.
  unfold R.v6, N.v6.
  rewrite ?node_12515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56346 (s : N.State) (i : N.Inputs) :
  R.v56346 (state s) (inputs i) = Zmod.unsigned (N.v56346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56346 s i)) at 1.
  unfold R.v56346, N.v56346.
  unfold R.v6, N.v6.
  rewrite ?node_12498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56347 (s : N.State) (i : N.Inputs) :
  R.v56347 (state s) (inputs i) = Zmod.unsigned (N.v56347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56347 s i)) at 1.
  unfold R.v56347, N.v56347.
  rewrite ?node_56345.
  rewrite ?node_56346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56348 (s : N.State) (i : N.Inputs) :
  R.v56348 (state s) (inputs i) = Zmod.unsigned (N.v56348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56348 s i)) at 1.
  unfold R.v56348, N.v56348.
  unfold R.v16484, N.v16484.
  rewrite ?node_56347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56349 (s : N.State) (i : N.Inputs) :
  R.v56349 (state s) (inputs i) = Zmod.unsigned (N.v56349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56349 s i)) at 1.
  unfold R.v56349, N.v56349.
  rewrite ?node_56344.
  rewrite ?node_56348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56350 (s : N.State) (i : N.Inputs) :
  R.v56350 (state s) (inputs i) = Zmod.unsigned (N.v56350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56350 s i)) at 1.
  unfold R.v56350, N.v56350.
  unfold R.v6, N.v6.
  rewrite ?node_56349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56351 (s : N.State) (i : N.Inputs) :
  R.v56351 (state s) (inputs i) = Zmod.unsigned (N.v56351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56351 s i)) at 1.
  unfold R.v56351, N.v56351.
  rewrite ?node_12520.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56352 (s : N.State) (i : N.Inputs) :
  R.v56352 (state s) (inputs i) = Zmod.unsigned (N.v56352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56352 s i)) at 1.
  unfold R.v56352, N.v56352.
  unfold R.v6, N.v6.
  rewrite ?node_12660.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56353 (s : N.State) (i : N.Inputs) :
  R.v56353 (state s) (inputs i) = Zmod.unsigned (N.v56353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56353 s i)) at 1.
  unfold R.v56353, N.v56353.
  rewrite ?node_56351.
  rewrite ?node_56352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56354 (s : N.State) (i : N.Inputs) :
  R.v56354 (state s) (inputs i) = Zmod.unsigned (N.v56354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56354 s i)) at 1.
  unfold R.v56354, N.v56354.
  rewrite ?node_56350.
  rewrite ?node_56353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56355 (s : N.State) (i : N.Inputs) :
  R.v56355 (state s) (inputs i) = Zmod.unsigned (N.v56355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56355 s i)) at 1.
  unfold R.v56355, N.v56355.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56356 (s : N.State) (i : N.Inputs) :
  R.v56356 (state s) (inputs i) = Zmod.unsigned (N.v56356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56356 s i)) at 1.
  unfold R.v56356, N.v56356.
  rewrite ?node_12527.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56357 (s : N.State) (i : N.Inputs) :
  R.v56357 (state s) (inputs i) = Zmod.unsigned (N.v56357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56357 s i)) at 1.
  unfold R.v56357, N.v56357.
  unfold R.v6, N.v6.
  rewrite ?node_12523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56358 (s : N.State) (i : N.Inputs) :
  R.v56358 (state s) (inputs i) = Zmod.unsigned (N.v56358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56358 s i)) at 1.
  unfold R.v56358, N.v56358.
  unfold R.v6, N.v6.
  rewrite ?node_12520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56359 (s : N.State) (i : N.Inputs) :
  R.v56359 (state s) (inputs i) = Zmod.unsigned (N.v56359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56359 s i)) at 1.
  unfold R.v56359, N.v56359.
  rewrite ?node_56357.
  rewrite ?node_56358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56360 (s : N.State) (i : N.Inputs) :
  R.v56360 (state s) (inputs i) = Zmod.unsigned (N.v56360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56360 s i)) at 1.
  unfold R.v56360, N.v56360.
  unfold R.v16484, N.v16484.
  rewrite ?node_56359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56361 (s : N.State) (i : N.Inputs) :
  R.v56361 (state s) (inputs i) = Zmod.unsigned (N.v56361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56361 s i)) at 1.
  unfold R.v56361, N.v56361.
  rewrite ?node_56356.
  rewrite ?node_56360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56362 (s : N.State) (i : N.Inputs) :
  R.v56362 (state s) (inputs i) = Zmod.unsigned (N.v56362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56362 s i)) at 1.
  unfold R.v56362, N.v56362.
  unfold R.v6, N.v6.
  rewrite ?node_56361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56363 (s : N.State) (i : N.Inputs) :
  R.v56363 (state s) (inputs i) = Zmod.unsigned (N.v56363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56363 s i)) at 1.
  unfold R.v56363, N.v56363.
  rewrite ?node_12528.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56364 (s : N.State) (i : N.Inputs) :
  R.v56364 (state s) (inputs i) = Zmod.unsigned (N.v56364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56364 s i)) at 1.
  unfold R.v56364, N.v56364.
  unfold R.v6, N.v6.
  rewrite ?node_12664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56365 (s : N.State) (i : N.Inputs) :
  R.v56365 (state s) (inputs i) = Zmod.unsigned (N.v56365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56365 s i)) at 1.
  unfold R.v56365, N.v56365.
  rewrite ?node_56363.
  rewrite ?node_56364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56366 (s : N.State) (i : N.Inputs) :
  R.v56366 (state s) (inputs i) = Zmod.unsigned (N.v56366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56366 s i)) at 1.
  unfold R.v56366, N.v56366.
  rewrite ?node_56362.
  rewrite ?node_56365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56367 (s : N.State) (i : N.Inputs) :
  R.v56367 (state s) (inputs i) = Zmod.unsigned (N.v56367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56367 s i)) at 1.
  unfold R.v56367, N.v56367.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56368 (s : N.State) (i : N.Inputs) :
  R.v56368 (state s) (inputs i) = Zmod.unsigned (N.v56368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56368 s i)) at 1.
  unfold R.v56368, N.v56368.
  rewrite ?node_12660.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56369 (s : N.State) (i : N.Inputs) :
  R.v56369 (state s) (inputs i) = Zmod.unsigned (N.v56369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56369 s i)) at 1.
  unfold R.v56369, N.v56369.
  rewrite ?node_12656.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56370 (s : N.State) (i : N.Inputs) :
  R.v56370 (state s) (inputs i) = Zmod.unsigned (N.v56370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56370 s i)) at 1.
  unfold R.v56370, N.v56370.
  rewrite ?node_12652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56371 (s : N.State) (i : N.Inputs) :
  R.v56371 (state s) (inputs i) = Zmod.unsigned (N.v56371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56371 s i)) at 1.
  unfold R.v56371, N.v56371.
  unfold R.v6, N.v6.
  rewrite ?node_12648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56372 (s : N.State) (i : N.Inputs) :
  R.v56372 (state s) (inputs i) = Zmod.unsigned (N.v56372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56372 s i)) at 1.
  unfold R.v56372, N.v56372.
  unfold R.v6, N.v6.
  rewrite ?node_12629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56373 (s : N.State) (i : N.Inputs) :
  R.v56373 (state s) (inputs i) = Zmod.unsigned (N.v56373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56373 s i)) at 1.
  unfold R.v56373, N.v56373.
  rewrite ?node_56371.
  rewrite ?node_56372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56374 (s : N.State) (i : N.Inputs) :
  R.v56374 (state s) (inputs i) = Zmod.unsigned (N.v56374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56374 s i)) at 1.
  unfold R.v56374, N.v56374.
  unfold R.v16484, N.v16484.
  rewrite ?node_56373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56375 (s : N.State) (i : N.Inputs) :
  R.v56375 (state s) (inputs i) = Zmod.unsigned (N.v56375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56375 s i)) at 1.
  unfold R.v56375, N.v56375.
  rewrite ?node_56368.
  rewrite ?node_56369.
  rewrite ?node_56370.
  rewrite ?node_56374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56376 (s : N.State) (i : N.Inputs) :
  R.v56376 (state s) (inputs i) = Zmod.unsigned (N.v56376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56376 s i)) at 1.
  unfold R.v56376, N.v56376.
  unfold R.v6, N.v6.
  rewrite ?node_56375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56377 (s : N.State) (i : N.Inputs) :
  R.v56377 (state s) (inputs i) = Zmod.unsigned (N.v56377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56377 s i)) at 1.
  unfold R.v56377, N.v56377.
  rewrite ?node_12661.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56378 (s : N.State) (i : N.Inputs) :
  R.v56378 (state s) (inputs i) = Zmod.unsigned (N.v56378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56378 s i)) at 1.
  unfold R.v56378, N.v56378.
  unfold R.v6, N.v6.
  rewrite ?node_12789.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56379 (s : N.State) (i : N.Inputs) :
  R.v56379 (state s) (inputs i) = Zmod.unsigned (N.v56379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56379 s i)) at 1.
  unfold R.v56379, N.v56379.
  unfold R.v6, N.v6.
  rewrite ?node_12793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56380 (s : N.State) (i : N.Inputs) :
  R.v56380 (state s) (inputs i) = Zmod.unsigned (N.v56380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56380 s i)) at 1.
  unfold R.v56380, N.v56380.
  rewrite ?node_56377.
  rewrite ?node_56378.
  rewrite ?node_56379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56381 (s : N.State) (i : N.Inputs) :
  R.v56381 (state s) (inputs i) = Zmod.unsigned (N.v56381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56381 s i)) at 1.
  unfold R.v56381, N.v56381.
  rewrite ?node_56376.
  rewrite ?node_56380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56382 (s : N.State) (i : N.Inputs) :
  R.v56382 (state s) (inputs i) = Zmod.unsigned (N.v56382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56382 s i)) at 1.
  unfold R.v56382, N.v56382.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56383 (s : N.State) (i : N.Inputs) :
  R.v56383 (state s) (inputs i) = Zmod.unsigned (N.v56383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56383 s i)) at 1.
  unfold R.v56383, N.v56383.
  rewrite ?node_12652.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56384 (s : N.State) (i : N.Inputs) :
  R.v56384 (state s) (inputs i) = Zmod.unsigned (N.v56384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56384 s i)) at 1.
  unfold R.v56384, N.v56384.
  unfold R.v6, N.v6.
  rewrite ?node_12648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56385 (s : N.State) (i : N.Inputs) :
  R.v56385 (state s) (inputs i) = Zmod.unsigned (N.v56385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56385 s i)) at 1.
  unfold R.v56385, N.v56385.
  unfold R.v6, N.v6.
  rewrite ?node_12629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56386 (s : N.State) (i : N.Inputs) :
  R.v56386 (state s) (inputs i) = Zmod.unsigned (N.v56386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56386 s i)) at 1.
  unfold R.v56386, N.v56386.
  rewrite ?node_56384.
  rewrite ?node_56385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56387 (s : N.State) (i : N.Inputs) :
  R.v56387 (state s) (inputs i) = Zmod.unsigned (N.v56387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56387 s i)) at 1.
  unfold R.v56387, N.v56387.
  unfold R.v16484, N.v16484.
  rewrite ?node_56386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56388 (s : N.State) (i : N.Inputs) :
  R.v56388 (state s) (inputs i) = Zmod.unsigned (N.v56388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56388 s i)) at 1.
  unfold R.v56388, N.v56388.
  rewrite ?node_56383.
  rewrite ?node_56387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56389 (s : N.State) (i : N.Inputs) :
  R.v56389 (state s) (inputs i) = Zmod.unsigned (N.v56389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56389 s i)) at 1.
  unfold R.v56389, N.v56389.
  unfold R.v6, N.v6.
  rewrite ?node_56388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56390 (s : N.State) (i : N.Inputs) :
  R.v56390 (state s) (inputs i) = Zmod.unsigned (N.v56390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56390 s i)) at 1.
  unfold R.v56390, N.v56390.
  rewrite ?node_12653.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56391 (s : N.State) (i : N.Inputs) :
  R.v56391 (state s) (inputs i) = Zmod.unsigned (N.v56391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56391 s i)) at 1.
  unfold R.v56391, N.v56391.
  unfold R.v6, N.v6.
  rewrite ?node_12789.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56392 (s : N.State) (i : N.Inputs) :
  R.v56392 (state s) (inputs i) = Zmod.unsigned (N.v56392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56392 s i)) at 1.
  unfold R.v56392, N.v56392.
  rewrite ?node_56390.
  rewrite ?node_56391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56393 (s : N.State) (i : N.Inputs) :
  R.v56393 (state s) (inputs i) = Zmod.unsigned (N.v56393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56393 s i)) at 1.
  unfold R.v56393, N.v56393.
  rewrite ?node_56389.
  rewrite ?node_56392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56394 (s : N.State) (i : N.Inputs) :
  R.v56394 (state s) (inputs i) = Zmod.unsigned (N.v56394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56394 s i)) at 1.
  unfold R.v56394, N.v56394.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56395 (s : N.State) (i : N.Inputs) :
  R.v56395 (state s) (inputs i) = Zmod.unsigned (N.v56395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56395 s i)) at 1.
  unfold R.v56395, N.v56395.
  rewrite ?node_12660.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56396 (s : N.State) (i : N.Inputs) :
  R.v56396 (state s) (inputs i) = Zmod.unsigned (N.v56396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56396 s i)) at 1.
  unfold R.v56396, N.v56396.
  unfold R.v6, N.v6.
  rewrite ?node_12656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56397 (s : N.State) (i : N.Inputs) :
  R.v56397 (state s) (inputs i) = Zmod.unsigned (N.v56397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56397 s i)) at 1.
  unfold R.v56397, N.v56397.
  unfold R.v6, N.v6.
  rewrite ?node_12653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56398 (s : N.State) (i : N.Inputs) :
  R.v56398 (state s) (inputs i) = Zmod.unsigned (N.v56398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56398 s i)) at 1.
  unfold R.v56398, N.v56398.
  rewrite ?node_56396.
  rewrite ?node_56397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56399 (s : N.State) (i : N.Inputs) :
  R.v56399 (state s) (inputs i) = Zmod.unsigned (N.v56399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56399 s i)) at 1.
  unfold R.v56399, N.v56399.
  unfold R.v16484, N.v16484.
  rewrite ?node_56398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56400 (s : N.State) (i : N.Inputs) :
  R.v56400 (state s) (inputs i) = Zmod.unsigned (N.v56400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56400 s i)) at 1.
  unfold R.v56400, N.v56400.
  rewrite ?node_56395.
  rewrite ?node_56399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56401 (s : N.State) (i : N.Inputs) :
  R.v56401 (state s) (inputs i) = Zmod.unsigned (N.v56401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56401 s i)) at 1.
  unfold R.v56401, N.v56401.
  unfold R.v6, N.v6.
  rewrite ?node_56400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56402 (s : N.State) (i : N.Inputs) :
  R.v56402 (state s) (inputs i) = Zmod.unsigned (N.v56402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56402 s i)) at 1.
  unfold R.v56402, N.v56402.
  rewrite ?node_12661.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56403 (s : N.State) (i : N.Inputs) :
  R.v56403 (state s) (inputs i) = Zmod.unsigned (N.v56403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56403 s i)) at 1.
  unfold R.v56403, N.v56403.
  unfold R.v6, N.v6.
  rewrite ?node_12793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56404 (s : N.State) (i : N.Inputs) :
  R.v56404 (state s) (inputs i) = Zmod.unsigned (N.v56404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56404 s i)) at 1.
  unfold R.v56404, N.v56404.
  rewrite ?node_56402.
  rewrite ?node_56403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56405 (s : N.State) (i : N.Inputs) :
  R.v56405 (state s) (inputs i) = Zmod.unsigned (N.v56405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56405 s i)) at 1.
  unfold R.v56405, N.v56405.
  rewrite ?node_56401.
  rewrite ?node_56404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56406 (s : N.State) (i : N.Inputs) :
  R.v56406 (state s) (inputs i) = Zmod.unsigned (N.v56406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56406 s i)) at 1.
  unfold R.v56406, N.v56406.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56407 (s : N.State) (i : N.Inputs) :
  R.v56407 (state s) (inputs i) = Zmod.unsigned (N.v56407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56407 s i)) at 1.
  unfold R.v56407, N.v56407.
  rewrite ?node_12789.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56408 (s : N.State) (i : N.Inputs) :
  R.v56408 (state s) (inputs i) = Zmod.unsigned (N.v56408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56408 s i)) at 1.
  unfold R.v56408, N.v56408.
  rewrite ?node_12785.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56409 (s : N.State) (i : N.Inputs) :
  R.v56409 (state s) (inputs i) = Zmod.unsigned (N.v56409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56409 s i)) at 1.
  unfold R.v56409, N.v56409.
  rewrite ?node_12781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56410 (s : N.State) (i : N.Inputs) :
  R.v56410 (state s) (inputs i) = Zmod.unsigned (N.v56410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56410 s i)) at 1.
  unfold R.v56410, N.v56410.
  unfold R.v6, N.v6.
  rewrite ?node_12777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56411 (s : N.State) (i : N.Inputs) :
  R.v56411 (state s) (inputs i) = Zmod.unsigned (N.v56411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56411 s i)) at 1.
  unfold R.v56411, N.v56411.
  unfold R.v6, N.v6.
  rewrite ?node_12760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56412 (s : N.State) (i : N.Inputs) :
  R.v56412 (state s) (inputs i) = Zmod.unsigned (N.v56412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56412 s i)) at 1.
  unfold R.v56412, N.v56412.
  rewrite ?node_56410.
  rewrite ?node_56411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56413 (s : N.State) (i : N.Inputs) :
  R.v56413 (state s) (inputs i) = Zmod.unsigned (N.v56413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56413 s i)) at 1.
  unfold R.v56413, N.v56413.
  unfold R.v16484, N.v16484.
  rewrite ?node_56412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56414 (s : N.State) (i : N.Inputs) :
  R.v56414 (state s) (inputs i) = Zmod.unsigned (N.v56414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56414 s i)) at 1.
  unfold R.v56414, N.v56414.
  rewrite ?node_56407.
  rewrite ?node_56408.
  rewrite ?node_56409.
  rewrite ?node_56413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56415 (s : N.State) (i : N.Inputs) :
  R.v56415 (state s) (inputs i) = Zmod.unsigned (N.v56415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56415 s i)) at 1.
  unfold R.v56415, N.v56415.
  unfold R.v6, N.v6.
  rewrite ?node_56414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56416 (s : N.State) (i : N.Inputs) :
  R.v56416 (state s) (inputs i) = Zmod.unsigned (N.v56416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56416 s i)) at 1.
  unfold R.v56416, N.v56416.
  rewrite ?node_12790.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56417 (s : N.State) (i : N.Inputs) :
  R.v56417 (state s) (inputs i) = Zmod.unsigned (N.v56417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56417 s i)) at 1.
  unfold R.v56417, N.v56417.
  unfold R.v6, N.v6.
  rewrite ?node_12917.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56418 (s : N.State) (i : N.Inputs) :
  R.v56418 (state s) (inputs i) = Zmod.unsigned (N.v56418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56418 s i)) at 1.
  unfold R.v56418, N.v56418.
  unfold R.v6, N.v6.
  rewrite ?node_12921.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56419 (s : N.State) (i : N.Inputs) :
  R.v56419 (state s) (inputs i) = Zmod.unsigned (N.v56419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56419 s i)) at 1.
  unfold R.v56419, N.v56419.
  rewrite ?node_56416.
  rewrite ?node_56417.
  rewrite ?node_56418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56420 (s : N.State) (i : N.Inputs) :
  R.v56420 (state s) (inputs i) = Zmod.unsigned (N.v56420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56420 s i)) at 1.
  unfold R.v56420, N.v56420.
  rewrite ?node_56415.
  rewrite ?node_56419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56421 (s : N.State) (i : N.Inputs) :
  R.v56421 (state s) (inputs i) = Zmod.unsigned (N.v56421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56421 s i)) at 1.
  unfold R.v56421, N.v56421.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56422 (s : N.State) (i : N.Inputs) :
  R.v56422 (state s) (inputs i) = Zmod.unsigned (N.v56422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56422 s i)) at 1.
  unfold R.v56422, N.v56422.
  rewrite ?node_12781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56423 (s : N.State) (i : N.Inputs) :
  R.v56423 (state s) (inputs i) = Zmod.unsigned (N.v56423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56423 s i)) at 1.
  unfold R.v56423, N.v56423.
  unfold R.v6, N.v6.
  rewrite ?node_12777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56424 (s : N.State) (i : N.Inputs) :
  R.v56424 (state s) (inputs i) = Zmod.unsigned (N.v56424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56424 s i)) at 1.
  unfold R.v56424, N.v56424.
  unfold R.v6, N.v6.
  rewrite ?node_12760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56425 (s : N.State) (i : N.Inputs) :
  R.v56425 (state s) (inputs i) = Zmod.unsigned (N.v56425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56425 s i)) at 1.
  unfold R.v56425, N.v56425.
  rewrite ?node_56423.
  rewrite ?node_56424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56426 (s : N.State) (i : N.Inputs) :
  R.v56426 (state s) (inputs i) = Zmod.unsigned (N.v56426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56426 s i)) at 1.
  unfold R.v56426, N.v56426.
  unfold R.v16484, N.v16484.
  rewrite ?node_56425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56427 (s : N.State) (i : N.Inputs) :
  R.v56427 (state s) (inputs i) = Zmod.unsigned (N.v56427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56427 s i)) at 1.
  unfold R.v56427, N.v56427.
  rewrite ?node_56422.
  rewrite ?node_56426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56428 (s : N.State) (i : N.Inputs) :
  R.v56428 (state s) (inputs i) = Zmod.unsigned (N.v56428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56428 s i)) at 1.
  unfold R.v56428, N.v56428.
  unfold R.v6, N.v6.
  rewrite ?node_56427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56429 (s : N.State) (i : N.Inputs) :
  R.v56429 (state s) (inputs i) = Zmod.unsigned (N.v56429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56429 s i)) at 1.
  unfold R.v56429, N.v56429.
  rewrite ?node_12782.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56430 (s : N.State) (i : N.Inputs) :
  R.v56430 (state s) (inputs i) = Zmod.unsigned (N.v56430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56430 s i)) at 1.
  unfold R.v56430, N.v56430.
  unfold R.v6, N.v6.
  rewrite ?node_12917.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56431 (s : N.State) (i : N.Inputs) :
  R.v56431 (state s) (inputs i) = Zmod.unsigned (N.v56431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56431 s i)) at 1.
  unfold R.v56431, N.v56431.
  rewrite ?node_56429.
  rewrite ?node_56430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56432 (s : N.State) (i : N.Inputs) :
  R.v56432 (state s) (inputs i) = Zmod.unsigned (N.v56432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56432 s i)) at 1.
  unfold R.v56432, N.v56432.
  rewrite ?node_56428.
  rewrite ?node_56431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56433 (s : N.State) (i : N.Inputs) :
  R.v56433 (state s) (inputs i) = Zmod.unsigned (N.v56433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56433 s i)) at 1.
  unfold R.v56433, N.v56433.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56434 (s : N.State) (i : N.Inputs) :
  R.v56434 (state s) (inputs i) = Zmod.unsigned (N.v56434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56434 s i)) at 1.
  unfold R.v56434, N.v56434.
  rewrite ?node_12789.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56435 (s : N.State) (i : N.Inputs) :
  R.v56435 (state s) (inputs i) = Zmod.unsigned (N.v56435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56435 s i)) at 1.
  unfold R.v56435, N.v56435.
  unfold R.v6, N.v6.
  rewrite ?node_12785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56436 (s : N.State) (i : N.Inputs) :
  R.v56436 (state s) (inputs i) = Zmod.unsigned (N.v56436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56436 s i)) at 1.
  unfold R.v56436, N.v56436.
  unfold R.v6, N.v6.
  rewrite ?node_12782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56437 (s : N.State) (i : N.Inputs) :
  R.v56437 (state s) (inputs i) = Zmod.unsigned (N.v56437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56437 s i)) at 1.
  unfold R.v56437, N.v56437.
  rewrite ?node_56435.
  rewrite ?node_56436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56438 (s : N.State) (i : N.Inputs) :
  R.v56438 (state s) (inputs i) = Zmod.unsigned (N.v56438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56438 s i)) at 1.
  unfold R.v56438, N.v56438.
  unfold R.v16484, N.v16484.
  rewrite ?node_56437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56439 (s : N.State) (i : N.Inputs) :
  R.v56439 (state s) (inputs i) = Zmod.unsigned (N.v56439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56439 s i)) at 1.
  unfold R.v56439, N.v56439.
  rewrite ?node_56434.
  rewrite ?node_56438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56440 (s : N.State) (i : N.Inputs) :
  R.v56440 (state s) (inputs i) = Zmod.unsigned (N.v56440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56440 s i)) at 1.
  unfold R.v56440, N.v56440.
  unfold R.v6, N.v6.
  rewrite ?node_56439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56441 (s : N.State) (i : N.Inputs) :
  R.v56441 (state s) (inputs i) = Zmod.unsigned (N.v56441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56441 s i)) at 1.
  unfold R.v56441, N.v56441.
  rewrite ?node_12790.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56442 (s : N.State) (i : N.Inputs) :
  R.v56442 (state s) (inputs i) = Zmod.unsigned (N.v56442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56442 s i)) at 1.
  unfold R.v56442, N.v56442.
  unfold R.v6, N.v6.
  rewrite ?node_12921.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56443 (s : N.State) (i : N.Inputs) :
  R.v56443 (state s) (inputs i) = Zmod.unsigned (N.v56443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56443 s i)) at 1.
  unfold R.v56443, N.v56443.
  rewrite ?node_56441.
  rewrite ?node_56442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56444 (s : N.State) (i : N.Inputs) :
  R.v56444 (state s) (inputs i) = Zmod.unsigned (N.v56444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56444 s i)) at 1.
  unfold R.v56444, N.v56444.
  rewrite ?node_56440.
  rewrite ?node_56443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56445 (s : N.State) (i : N.Inputs) :
  R.v56445 (state s) (inputs i) = Zmod.unsigned (N.v56445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56445 s i)) at 1.
  unfold R.v56445, N.v56445.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56446 (s : N.State) (i : N.Inputs) :
  R.v56446 (state s) (inputs i) = Zmod.unsigned (N.v56446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56446 s i)) at 1.
  unfold R.v56446, N.v56446.
  rewrite ?node_12917.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56447 (s : N.State) (i : N.Inputs) :
  R.v56447 (state s) (inputs i) = Zmod.unsigned (N.v56447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56447 s i)) at 1.
  unfold R.v56447, N.v56447.
  rewrite ?node_12913.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56448 (s : N.State) (i : N.Inputs) :
  R.v56448 (state s) (inputs i) = Zmod.unsigned (N.v56448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56448 s i)) at 1.
  unfold R.v56448, N.v56448.
  rewrite ?node_12909.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56449 (s : N.State) (i : N.Inputs) :
  R.v56449 (state s) (inputs i) = Zmod.unsigned (N.v56449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56449 s i)) at 1.
  unfold R.v56449, N.v56449.
  unfold R.v6, N.v6.
  rewrite ?node_12905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56450 (s : N.State) (i : N.Inputs) :
  R.v56450 (state s) (inputs i) = Zmod.unsigned (N.v56450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56450 s i)) at 1.
  unfold R.v56450, N.v56450.
  unfold R.v6, N.v6.
  rewrite ?node_12888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56451 (s : N.State) (i : N.Inputs) :
  R.v56451 (state s) (inputs i) = Zmod.unsigned (N.v56451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56451 s i)) at 1.
  unfold R.v56451, N.v56451.
  rewrite ?node_56449.
  rewrite ?node_56450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56452 (s : N.State) (i : N.Inputs) :
  R.v56452 (state s) (inputs i) = Zmod.unsigned (N.v56452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56452 s i)) at 1.
  unfold R.v56452, N.v56452.
  unfold R.v16484, N.v16484.
  rewrite ?node_56451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56453 (s : N.State) (i : N.Inputs) :
  R.v56453 (state s) (inputs i) = Zmod.unsigned (N.v56453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56453 s i)) at 1.
  unfold R.v56453, N.v56453.
  rewrite ?node_56446.
  rewrite ?node_56447.
  rewrite ?node_56448.
  rewrite ?node_56452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56454 (s : N.State) (i : N.Inputs) :
  R.v56454 (state s) (inputs i) = Zmod.unsigned (N.v56454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56454 s i)) at 1.
  unfold R.v56454, N.v56454.
  unfold R.v6, N.v6.
  rewrite ?node_56453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56455 (s : N.State) (i : N.Inputs) :
  R.v56455 (state s) (inputs i) = Zmod.unsigned (N.v56455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56455 s i)) at 1.
  unfold R.v56455, N.v56455.
  rewrite ?node_12918.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56456 (s : N.State) (i : N.Inputs) :
  R.v56456 (state s) (inputs i) = Zmod.unsigned (N.v56456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56456 s i)) at 1.
  unfold R.v56456, N.v56456.
  unfold R.v6, N.v6.
  rewrite ?node_13043.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56457 (s : N.State) (i : N.Inputs) :
  R.v56457 (state s) (inputs i) = Zmod.unsigned (N.v56457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56457 s i)) at 1.
  unfold R.v56457, N.v56457.
  unfold R.v6, N.v6.
  rewrite ?node_13047.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56458 (s : N.State) (i : N.Inputs) :
  R.v56458 (state s) (inputs i) = Zmod.unsigned (N.v56458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56458 s i)) at 1.
  unfold R.v56458, N.v56458.
  rewrite ?node_56455.
  rewrite ?node_56456.
  rewrite ?node_56457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56459 (s : N.State) (i : N.Inputs) :
  R.v56459 (state s) (inputs i) = Zmod.unsigned (N.v56459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56459 s i)) at 1.
  unfold R.v56459, N.v56459.
  rewrite ?node_56454.
  rewrite ?node_56458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56460 (s : N.State) (i : N.Inputs) :
  R.v56460 (state s) (inputs i) = Zmod.unsigned (N.v56460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56460 s i)) at 1.
  unfold R.v56460, N.v56460.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56461 (s : N.State) (i : N.Inputs) :
  R.v56461 (state s) (inputs i) = Zmod.unsigned (N.v56461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56461 s i)) at 1.
  unfold R.v56461, N.v56461.
  rewrite ?node_12909.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56462 (s : N.State) (i : N.Inputs) :
  R.v56462 (state s) (inputs i) = Zmod.unsigned (N.v56462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56462 s i)) at 1.
  unfold R.v56462, N.v56462.
  unfold R.v6, N.v6.
  rewrite ?node_12905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56463 (s : N.State) (i : N.Inputs) :
  R.v56463 (state s) (inputs i) = Zmod.unsigned (N.v56463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56463 s i)) at 1.
  unfold R.v56463, N.v56463.
  unfold R.v6, N.v6.
  rewrite ?node_12888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56464 (s : N.State) (i : N.Inputs) :
  R.v56464 (state s) (inputs i) = Zmod.unsigned (N.v56464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56464 s i)) at 1.
  unfold R.v56464, N.v56464.
  rewrite ?node_56462.
  rewrite ?node_56463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56465 (s : N.State) (i : N.Inputs) :
  R.v56465 (state s) (inputs i) = Zmod.unsigned (N.v56465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56465 s i)) at 1.
  unfold R.v56465, N.v56465.
  unfold R.v16484, N.v16484.
  rewrite ?node_56464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56466 (s : N.State) (i : N.Inputs) :
  R.v56466 (state s) (inputs i) = Zmod.unsigned (N.v56466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56466 s i)) at 1.
  unfold R.v56466, N.v56466.
  rewrite ?node_56461.
  rewrite ?node_56465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56467 (s : N.State) (i : N.Inputs) :
  R.v56467 (state s) (inputs i) = Zmod.unsigned (N.v56467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56467 s i)) at 1.
  unfold R.v56467, N.v56467.
  unfold R.v6, N.v6.
  rewrite ?node_56466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56468 (s : N.State) (i : N.Inputs) :
  R.v56468 (state s) (inputs i) = Zmod.unsigned (N.v56468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56468 s i)) at 1.
  unfold R.v56468, N.v56468.
  rewrite ?node_12910.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56469 (s : N.State) (i : N.Inputs) :
  R.v56469 (state s) (inputs i) = Zmod.unsigned (N.v56469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56469 s i)) at 1.
  unfold R.v56469, N.v56469.
  unfold R.v6, N.v6.
  rewrite ?node_13043.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56470 (s : N.State) (i : N.Inputs) :
  R.v56470 (state s) (inputs i) = Zmod.unsigned (N.v56470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56470 s i)) at 1.
  unfold R.v56470, N.v56470.
  rewrite ?node_56468.
  rewrite ?node_56469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56471 (s : N.State) (i : N.Inputs) :
  R.v56471 (state s) (inputs i) = Zmod.unsigned (N.v56471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56471 s i)) at 1.
  unfold R.v56471, N.v56471.
  rewrite ?node_56467.
  rewrite ?node_56470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56472 (s : N.State) (i : N.Inputs) :
  R.v56472 (state s) (inputs i) = Zmod.unsigned (N.v56472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56472 s i)) at 1.
  unfold R.v56472, N.v56472.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56473 (s : N.State) (i : N.Inputs) :
  R.v56473 (state s) (inputs i) = Zmod.unsigned (N.v56473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56473 s i)) at 1.
  unfold R.v56473, N.v56473.
  rewrite ?node_12917.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56474 (s : N.State) (i : N.Inputs) :
  R.v56474 (state s) (inputs i) = Zmod.unsigned (N.v56474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56474 s i)) at 1.
  unfold R.v56474, N.v56474.
  unfold R.v6, N.v6.
  rewrite ?node_12913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56475 (s : N.State) (i : N.Inputs) :
  R.v56475 (state s) (inputs i) = Zmod.unsigned (N.v56475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56475 s i)) at 1.
  unfold R.v56475, N.v56475.
  unfold R.v6, N.v6.
  rewrite ?node_12910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56476 (s : N.State) (i : N.Inputs) :
  R.v56476 (state s) (inputs i) = Zmod.unsigned (N.v56476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56476 s i)) at 1.
  unfold R.v56476, N.v56476.
  rewrite ?node_56474.
  rewrite ?node_56475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56477 (s : N.State) (i : N.Inputs) :
  R.v56477 (state s) (inputs i) = Zmod.unsigned (N.v56477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56477 s i)) at 1.
  unfold R.v56477, N.v56477.
  unfold R.v16484, N.v16484.
  rewrite ?node_56476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56478 (s : N.State) (i : N.Inputs) :
  R.v56478 (state s) (inputs i) = Zmod.unsigned (N.v56478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56478 s i)) at 1.
  unfold R.v56478, N.v56478.
  rewrite ?node_56473.
  rewrite ?node_56477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56479 (s : N.State) (i : N.Inputs) :
  R.v56479 (state s) (inputs i) = Zmod.unsigned (N.v56479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56479 s i)) at 1.
  unfold R.v56479, N.v56479.
  unfold R.v6, N.v6.
  rewrite ?node_56478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56480 (s : N.State) (i : N.Inputs) :
  R.v56480 (state s) (inputs i) = Zmod.unsigned (N.v56480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56480 s i)) at 1.
  unfold R.v56480, N.v56480.
  rewrite ?node_12918.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56481 (s : N.State) (i : N.Inputs) :
  R.v56481 (state s) (inputs i) = Zmod.unsigned (N.v56481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56481 s i)) at 1.
  unfold R.v56481, N.v56481.
  unfold R.v6, N.v6.
  rewrite ?node_13047.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56482 (s : N.State) (i : N.Inputs) :
  R.v56482 (state s) (inputs i) = Zmod.unsigned (N.v56482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56482 s i)) at 1.
  unfold R.v56482, N.v56482.
  rewrite ?node_56480.
  rewrite ?node_56481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56483 (s : N.State) (i : N.Inputs) :
  R.v56483 (state s) (inputs i) = Zmod.unsigned (N.v56483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56483 s i)) at 1.
  unfold R.v56483, N.v56483.
  rewrite ?node_56479.
  rewrite ?node_56482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56484 (s : N.State) (i : N.Inputs) :
  R.v56484 (state s) (inputs i) = Zmod.unsigned (N.v56484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56484 s i)) at 1.
  unfold R.v56484, N.v56484.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56485 (s : N.State) (i : N.Inputs) :
  R.v56485 (state s) (inputs i) = Zmod.unsigned (N.v56485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56485 s i)) at 1.
  unfold R.v56485, N.v56485.
  rewrite ?node_13043.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56486 (s : N.State) (i : N.Inputs) :
  R.v56486 (state s) (inputs i) = Zmod.unsigned (N.v56486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56486 s i)) at 1.
  unfold R.v56486, N.v56486.
  rewrite ?node_13039.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56487 (s : N.State) (i : N.Inputs) :
  R.v56487 (state s) (inputs i) = Zmod.unsigned (N.v56487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56487 s i)) at 1.
  unfold R.v56487, N.v56487.
  rewrite ?node_13035.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56488 (s : N.State) (i : N.Inputs) :
  R.v56488 (state s) (inputs i) = Zmod.unsigned (N.v56488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56488 s i)) at 1.
  unfold R.v56488, N.v56488.
  unfold R.v6, N.v6.
  rewrite ?node_13031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56489 (s : N.State) (i : N.Inputs) :
  R.v56489 (state s) (inputs i) = Zmod.unsigned (N.v56489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56489 s i)) at 1.
  unfold R.v56489, N.v56489.
  unfold R.v6, N.v6.
  rewrite ?node_13014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56490 (s : N.State) (i : N.Inputs) :
  R.v56490 (state s) (inputs i) = Zmod.unsigned (N.v56490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56490 s i)) at 1.
  unfold R.v56490, N.v56490.
  rewrite ?node_56488.
  rewrite ?node_56489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56491 (s : N.State) (i : N.Inputs) :
  R.v56491 (state s) (inputs i) = Zmod.unsigned (N.v56491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56491 s i)) at 1.
  unfold R.v56491, N.v56491.
  unfold R.v16484, N.v16484.
  rewrite ?node_56490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56492 (s : N.State) (i : N.Inputs) :
  R.v56492 (state s) (inputs i) = Zmod.unsigned (N.v56492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56492 s i)) at 1.
  unfold R.v56492, N.v56492.
  rewrite ?node_56485.
  rewrite ?node_56486.
  rewrite ?node_56487.
  rewrite ?node_56491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56493 (s : N.State) (i : N.Inputs) :
  R.v56493 (state s) (inputs i) = Zmod.unsigned (N.v56493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56493 s i)) at 1.
  unfold R.v56493, N.v56493.
  unfold R.v6, N.v6.
  rewrite ?node_56492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56494 (s : N.State) (i : N.Inputs) :
  R.v56494 (state s) (inputs i) = Zmod.unsigned (N.v56494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56494 s i)) at 1.
  unfold R.v56494, N.v56494.
  rewrite ?node_13044.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56495 (s : N.State) (i : N.Inputs) :
  R.v56495 (state s) (inputs i) = Zmod.unsigned (N.v56495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56495 s i)) at 1.
  unfold R.v56495, N.v56495.
  unfold R.v6, N.v6.
  rewrite ?node_13168.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56496 (s : N.State) (i : N.Inputs) :
  R.v56496 (state s) (inputs i) = Zmod.unsigned (N.v56496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56496 s i)) at 1.
  unfold R.v56496, N.v56496.
  unfold R.v6, N.v6.
  rewrite ?node_13172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56497 (s : N.State) (i : N.Inputs) :
  R.v56497 (state s) (inputs i) = Zmod.unsigned (N.v56497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56497 s i)) at 1.
  unfold R.v56497, N.v56497.
  rewrite ?node_56494.
  rewrite ?node_56495.
  rewrite ?node_56496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56498 (s : N.State) (i : N.Inputs) :
  R.v56498 (state s) (inputs i) = Zmod.unsigned (N.v56498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56498 s i)) at 1.
  unfold R.v56498, N.v56498.
  rewrite ?node_56493.
  rewrite ?node_56497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56499 (s : N.State) (i : N.Inputs) :
  R.v56499 (state s) (inputs i) = Zmod.unsigned (N.v56499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56499 s i)) at 1.
  unfold R.v56499, N.v56499.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56500 (s : N.State) (i : N.Inputs) :
  R.v56500 (state s) (inputs i) = Zmod.unsigned (N.v56500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56500 s i)) at 1.
  unfold R.v56500, N.v56500.
  rewrite ?node_13035.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56501 (s : N.State) (i : N.Inputs) :
  R.v56501 (state s) (inputs i) = Zmod.unsigned (N.v56501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56501 s i)) at 1.
  unfold R.v56501, N.v56501.
  unfold R.v6, N.v6.
  rewrite ?node_13031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56502 (s : N.State) (i : N.Inputs) :
  R.v56502 (state s) (inputs i) = Zmod.unsigned (N.v56502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56502 s i)) at 1.
  unfold R.v56502, N.v56502.
  unfold R.v6, N.v6.
  rewrite ?node_13014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56503 (s : N.State) (i : N.Inputs) :
  R.v56503 (state s) (inputs i) = Zmod.unsigned (N.v56503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56503 s i)) at 1.
  unfold R.v56503, N.v56503.
  rewrite ?node_56501.
  rewrite ?node_56502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56504 (s : N.State) (i : N.Inputs) :
  R.v56504 (state s) (inputs i) = Zmod.unsigned (N.v56504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56504 s i)) at 1.
  unfold R.v56504, N.v56504.
  unfold R.v16484, N.v16484.
  rewrite ?node_56503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56505 (s : N.State) (i : N.Inputs) :
  R.v56505 (state s) (inputs i) = Zmod.unsigned (N.v56505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56505 s i)) at 1.
  unfold R.v56505, N.v56505.
  rewrite ?node_56500.
  rewrite ?node_56504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56506 (s : N.State) (i : N.Inputs) :
  R.v56506 (state s) (inputs i) = Zmod.unsigned (N.v56506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56506 s i)) at 1.
  unfold R.v56506, N.v56506.
  unfold R.v6, N.v6.
  rewrite ?node_56505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56507 (s : N.State) (i : N.Inputs) :
  R.v56507 (state s) (inputs i) = Zmod.unsigned (N.v56507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56507 s i)) at 1.
  unfold R.v56507, N.v56507.
  rewrite ?node_13036.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56508 (s : N.State) (i : N.Inputs) :
  R.v56508 (state s) (inputs i) = Zmod.unsigned (N.v56508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56508 s i)) at 1.
  unfold R.v56508, N.v56508.
  unfold R.v6, N.v6.
  rewrite ?node_13168.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56509 (s : N.State) (i : N.Inputs) :
  R.v56509 (state s) (inputs i) = Zmod.unsigned (N.v56509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56509 s i)) at 1.
  unfold R.v56509, N.v56509.
  rewrite ?node_56507.
  rewrite ?node_56508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56510 (s : N.State) (i : N.Inputs) :
  R.v56510 (state s) (inputs i) = Zmod.unsigned (N.v56510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56510 s i)) at 1.
  unfold R.v56510, N.v56510.
  rewrite ?node_56506.
  rewrite ?node_56509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56511 (s : N.State) (i : N.Inputs) :
  R.v56511 (state s) (inputs i) = Zmod.unsigned (N.v56511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56511 s i)) at 1.
  unfold R.v56511, N.v56511.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56512 (s : N.State) (i : N.Inputs) :
  R.v56512 (state s) (inputs i) = Zmod.unsigned (N.v56512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56512 s i)) at 1.
  unfold R.v56512, N.v56512.
  rewrite ?node_13043.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56513 (s : N.State) (i : N.Inputs) :
  R.v56513 (state s) (inputs i) = Zmod.unsigned (N.v56513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56513 s i)) at 1.
  unfold R.v56513, N.v56513.
  unfold R.v6, N.v6.
  rewrite ?node_13039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56514 (s : N.State) (i : N.Inputs) :
  R.v56514 (state s) (inputs i) = Zmod.unsigned (N.v56514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56514 s i)) at 1.
  unfold R.v56514, N.v56514.
  unfold R.v6, N.v6.
  rewrite ?node_13036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56515 (s : N.State) (i : N.Inputs) :
  R.v56515 (state s) (inputs i) = Zmod.unsigned (N.v56515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56515 s i)) at 1.
  unfold R.v56515, N.v56515.
  rewrite ?node_56513.
  rewrite ?node_56514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56516 (s : N.State) (i : N.Inputs) :
  R.v56516 (state s) (inputs i) = Zmod.unsigned (N.v56516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56516 s i)) at 1.
  unfold R.v56516, N.v56516.
  unfold R.v16484, N.v16484.
  rewrite ?node_56515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56517 (s : N.State) (i : N.Inputs) :
  R.v56517 (state s) (inputs i) = Zmod.unsigned (N.v56517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56517 s i)) at 1.
  unfold R.v56517, N.v56517.
  rewrite ?node_56512.
  rewrite ?node_56516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56518 (s : N.State) (i : N.Inputs) :
  R.v56518 (state s) (inputs i) = Zmod.unsigned (N.v56518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56518 s i)) at 1.
  unfold R.v56518, N.v56518.
  unfold R.v6, N.v6.
  rewrite ?node_56517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56519 (s : N.State) (i : N.Inputs) :
  R.v56519 (state s) (inputs i) = Zmod.unsigned (N.v56519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56519 s i)) at 1.
  unfold R.v56519, N.v56519.
  rewrite ?node_13044.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56520 (s : N.State) (i : N.Inputs) :
  R.v56520 (state s) (inputs i) = Zmod.unsigned (N.v56520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56520 s i)) at 1.
  unfold R.v56520, N.v56520.
  unfold R.v6, N.v6.
  rewrite ?node_13172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56521 (s : N.State) (i : N.Inputs) :
  R.v56521 (state s) (inputs i) = Zmod.unsigned (N.v56521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56521 s i)) at 1.
  unfold R.v56521, N.v56521.
  rewrite ?node_56519.
  rewrite ?node_56520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56522 (s : N.State) (i : N.Inputs) :
  R.v56522 (state s) (inputs i) = Zmod.unsigned (N.v56522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56522 s i)) at 1.
  unfold R.v56522, N.v56522.
  rewrite ?node_56518.
  rewrite ?node_56521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56523 (s : N.State) (i : N.Inputs) :
  R.v56523 (state s) (inputs i) = Zmod.unsigned (N.v56523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56523 s i)) at 1.
  unfold R.v56523, N.v56523.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56524 (s : N.State) (i : N.Inputs) :
  R.v56524 (state s) (inputs i) = Zmod.unsigned (N.v56524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56524 s i)) at 1.
  unfold R.v56524, N.v56524.
  rewrite ?node_13168.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56525 (s : N.State) (i : N.Inputs) :
  R.v56525 (state s) (inputs i) = Zmod.unsigned (N.v56525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56525 s i)) at 1.
  unfold R.v56525, N.v56525.
  rewrite ?node_13164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56526 (s : N.State) (i : N.Inputs) :
  R.v56526 (state s) (inputs i) = Zmod.unsigned (N.v56526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56526 s i)) at 1.
  unfold R.v56526, N.v56526.
  rewrite ?node_13160.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56527 (s : N.State) (i : N.Inputs) :
  R.v56527 (state s) (inputs i) = Zmod.unsigned (N.v56527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56527 s i)) at 1.
  unfold R.v56527, N.v56527.
  unfold R.v6, N.v6.
  rewrite ?node_13156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56528 (s : N.State) (i : N.Inputs) :
  R.v56528 (state s) (inputs i) = Zmod.unsigned (N.v56528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56528 s i)) at 1.
  unfold R.v56528, N.v56528.
  unfold R.v6, N.v6.
  rewrite ?node_13139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56529 (s : N.State) (i : N.Inputs) :
  R.v56529 (state s) (inputs i) = Zmod.unsigned (N.v56529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56529 s i)) at 1.
  unfold R.v56529, N.v56529.
  rewrite ?node_56527.
  rewrite ?node_56528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56530 (s : N.State) (i : N.Inputs) :
  R.v56530 (state s) (inputs i) = Zmod.unsigned (N.v56530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56530 s i)) at 1.
  unfold R.v56530, N.v56530.
  unfold R.v16484, N.v16484.
  rewrite ?node_56529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56531 (s : N.State) (i : N.Inputs) :
  R.v56531 (state s) (inputs i) = Zmod.unsigned (N.v56531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56531 s i)) at 1.
  unfold R.v56531, N.v56531.
  rewrite ?node_56524.
  rewrite ?node_56525.
  rewrite ?node_56526.
  rewrite ?node_56530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56532 (s : N.State) (i : N.Inputs) :
  R.v56532 (state s) (inputs i) = Zmod.unsigned (N.v56532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56532 s i)) at 1.
  unfold R.v56532, N.v56532.
  unfold R.v6, N.v6.
  rewrite ?node_56531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56533 (s : N.State) (i : N.Inputs) :
  R.v56533 (state s) (inputs i) = Zmod.unsigned (N.v56533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56533 s i)) at 1.
  unfold R.v56533, N.v56533.
  rewrite ?node_13169.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56534 (s : N.State) (i : N.Inputs) :
  R.v56534 (state s) (inputs i) = Zmod.unsigned (N.v56534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56534 s i)) at 1.
  unfold R.v56534, N.v56534.
  unfold R.v6, N.v6.
  rewrite ?node_13285.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56535 (s : N.State) (i : N.Inputs) :
  R.v56535 (state s) (inputs i) = Zmod.unsigned (N.v56535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56535 s i)) at 1.
  unfold R.v56535, N.v56535.
  unfold R.v6, N.v6.
  rewrite ?node_13293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56536 (s : N.State) (i : N.Inputs) :
  R.v56536 (state s) (inputs i) = Zmod.unsigned (N.v56536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56536 s i)) at 1.
  unfold R.v56536, N.v56536.
  rewrite ?node_56533.
  rewrite ?node_56534.
  rewrite ?node_56535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56537 (s : N.State) (i : N.Inputs) :
  R.v56537 (state s) (inputs i) = Zmod.unsigned (N.v56537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56537 s i)) at 1.
  unfold R.v56537, N.v56537.
  rewrite ?node_56532.
  rewrite ?node_56536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56538 (s : N.State) (i : N.Inputs) :
  R.v56538 (state s) (inputs i) = Zmod.unsigned (N.v56538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56538 s i)) at 1.
  unfold R.v56538, N.v56538.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56539 (s : N.State) (i : N.Inputs) :
  R.v56539 (state s) (inputs i) = Zmod.unsigned (N.v56539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56539 s i)) at 1.
  unfold R.v56539, N.v56539.
  rewrite ?node_13160.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56540 (s : N.State) (i : N.Inputs) :
  R.v56540 (state s) (inputs i) = Zmod.unsigned (N.v56540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56540 s i)) at 1.
  unfold R.v56540, N.v56540.
  unfold R.v6, N.v6.
  rewrite ?node_13156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56541 (s : N.State) (i : N.Inputs) :
  R.v56541 (state s) (inputs i) = Zmod.unsigned (N.v56541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56541 s i)) at 1.
  unfold R.v56541, N.v56541.
  unfold R.v6, N.v6.
  rewrite ?node_13139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56542 (s : N.State) (i : N.Inputs) :
  R.v56542 (state s) (inputs i) = Zmod.unsigned (N.v56542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56542 s i)) at 1.
  unfold R.v56542, N.v56542.
  rewrite ?node_56540.
  rewrite ?node_56541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56543 (s : N.State) (i : N.Inputs) :
  R.v56543 (state s) (inputs i) = Zmod.unsigned (N.v56543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56543 s i)) at 1.
  unfold R.v56543, N.v56543.
  unfold R.v16484, N.v16484.
  rewrite ?node_56542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56544 (s : N.State) (i : N.Inputs) :
  R.v56544 (state s) (inputs i) = Zmod.unsigned (N.v56544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56544 s i)) at 1.
  unfold R.v56544, N.v56544.
  rewrite ?node_56539.
  rewrite ?node_56543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56545 (s : N.State) (i : N.Inputs) :
  R.v56545 (state s) (inputs i) = Zmod.unsigned (N.v56545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56545 s i)) at 1.
  unfold R.v56545, N.v56545.
  unfold R.v6, N.v6.
  rewrite ?node_56544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56546 (s : N.State) (i : N.Inputs) :
  R.v56546 (state s) (inputs i) = Zmod.unsigned (N.v56546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56546 s i)) at 1.
  unfold R.v56546, N.v56546.
  rewrite ?node_13161.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56547 (s : N.State) (i : N.Inputs) :
  R.v56547 (state s) (inputs i) = Zmod.unsigned (N.v56547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56547 s i)) at 1.
  unfold R.v56547, N.v56547.
  unfold R.v6, N.v6.
  rewrite ?node_13285.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56548 (s : N.State) (i : N.Inputs) :
  R.v56548 (state s) (inputs i) = Zmod.unsigned (N.v56548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56548 s i)) at 1.
  unfold R.v56548, N.v56548.
  rewrite ?node_56546.
  rewrite ?node_56547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56549 (s : N.State) (i : N.Inputs) :
  R.v56549 (state s) (inputs i) = Zmod.unsigned (N.v56549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56549 s i)) at 1.
  unfold R.v56549, N.v56549.
  rewrite ?node_56545.
  rewrite ?node_56548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56550 (s : N.State) (i : N.Inputs) :
  R.v56550 (state s) (inputs i) = Zmod.unsigned (N.v56550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56550 s i)) at 1.
  unfold R.v56550, N.v56550.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56551 (s : N.State) (i : N.Inputs) :
  R.v56551 (state s) (inputs i) = Zmod.unsigned (N.v56551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56551 s i)) at 1.
  unfold R.v56551, N.v56551.
  rewrite ?node_13168.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56552 (s : N.State) (i : N.Inputs) :
  R.v56552 (state s) (inputs i) = Zmod.unsigned (N.v56552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56552 s i)) at 1.
  unfold R.v56552, N.v56552.
  unfold R.v6, N.v6.
  rewrite ?node_13164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56553 (s : N.State) (i : N.Inputs) :
  R.v56553 (state s) (inputs i) = Zmod.unsigned (N.v56553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56553 s i)) at 1.
  unfold R.v56553, N.v56553.
  unfold R.v6, N.v6.
  rewrite ?node_13161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56554 (s : N.State) (i : N.Inputs) :
  R.v56554 (state s) (inputs i) = Zmod.unsigned (N.v56554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56554 s i)) at 1.
  unfold R.v56554, N.v56554.
  rewrite ?node_56552.
  rewrite ?node_56553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56555 (s : N.State) (i : N.Inputs) :
  R.v56555 (state s) (inputs i) = Zmod.unsigned (N.v56555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56555 s i)) at 1.
  unfold R.v56555, N.v56555.
  unfold R.v16484, N.v16484.
  rewrite ?node_56554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56556 (s : N.State) (i : N.Inputs) :
  R.v56556 (state s) (inputs i) = Zmod.unsigned (N.v56556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56556 s i)) at 1.
  unfold R.v56556, N.v56556.
  rewrite ?node_56551.
  rewrite ?node_56555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56557 (s : N.State) (i : N.Inputs) :
  R.v56557 (state s) (inputs i) = Zmod.unsigned (N.v56557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56557 s i)) at 1.
  unfold R.v56557, N.v56557.
  unfold R.v6, N.v6.
  rewrite ?node_56556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56558 (s : N.State) (i : N.Inputs) :
  R.v56558 (state s) (inputs i) = Zmod.unsigned (N.v56558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56558 s i)) at 1.
  unfold R.v56558, N.v56558.
  rewrite ?node_13169.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56559 (s : N.State) (i : N.Inputs) :
  R.v56559 (state s) (inputs i) = Zmod.unsigned (N.v56559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56559 s i)) at 1.
  unfold R.v56559, N.v56559.
  unfold R.v6, N.v6.
  rewrite ?node_13293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56560 (s : N.State) (i : N.Inputs) :
  R.v56560 (state s) (inputs i) = Zmod.unsigned (N.v56560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56560 s i)) at 1.
  unfold R.v56560, N.v56560.
  rewrite ?node_56558.
  rewrite ?node_56559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56561 (s : N.State) (i : N.Inputs) :
  R.v56561 (state s) (inputs i) = Zmod.unsigned (N.v56561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56561 s i)) at 1.
  unfold R.v56561, N.v56561.
  rewrite ?node_56557.
  rewrite ?node_56560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56562 (s : N.State) (i : N.Inputs) :
  R.v56562 (state s) (inputs i) = Zmod.unsigned (N.v56562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56562 s i)) at 1.
  unfold R.v56562, N.v56562.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56563 (s : N.State) (i : N.Inputs) :
  R.v56563 (state s) (inputs i) = Zmod.unsigned (N.v56563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56563 s i)) at 1.
  unfold R.v56563, N.v56563.
  rewrite ?node_13285.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56564 (s : N.State) (i : N.Inputs) :
  R.v56564 (state s) (inputs i) = Zmod.unsigned (N.v56564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56564 s i)) at 1.
  unfold R.v56564, N.v56564.
  rewrite ?node_13281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56565 (s : N.State) (i : N.Inputs) :
  R.v56565 (state s) (inputs i) = Zmod.unsigned (N.v56565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56565 s i)) at 1.
  unfold R.v56565, N.v56565.
  rewrite ?node_13277.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56566 (s : N.State) (i : N.Inputs) :
  R.v56566 (state s) (inputs i) = Zmod.unsigned (N.v56566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56566 s i)) at 1.
  unfold R.v56566, N.v56566.
  unfold R.v6, N.v6.
  rewrite ?node_13273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56567 (s : N.State) (i : N.Inputs) :
  R.v56567 (state s) (inputs i) = Zmod.unsigned (N.v56567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56567 s i)) at 1.
  unfold R.v56567, N.v56567.
  unfold R.v6, N.v6.
  rewrite ?node_13266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56568 (s : N.State) (i : N.Inputs) :
  R.v56568 (state s) (inputs i) = Zmod.unsigned (N.v56568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56568 s i)) at 1.
  unfold R.v56568, N.v56568.
  rewrite ?node_56566.
  rewrite ?node_56567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56569 (s : N.State) (i : N.Inputs) :
  R.v56569 (state s) (inputs i) = Zmod.unsigned (N.v56569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56569 s i)) at 1.
  unfold R.v56569, N.v56569.
  unfold R.v16484, N.v16484.
  rewrite ?node_56568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56570 (s : N.State) (i : N.Inputs) :
  R.v56570 (state s) (inputs i) = Zmod.unsigned (N.v56570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56570 s i)) at 1.
  unfold R.v56570, N.v56570.
  rewrite ?node_56563.
  rewrite ?node_56564.
  rewrite ?node_56565.
  rewrite ?node_56569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56571 (s : N.State) (i : N.Inputs) :
  R.v56571 (state s) (inputs i) = Zmod.unsigned (N.v56571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56571 s i)) at 1.
  unfold R.v56571, N.v56571.
  unfold R.v6, N.v6.
  rewrite ?node_56570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56572 (s : N.State) (i : N.Inputs) :
  R.v56572 (state s) (inputs i) = Zmod.unsigned (N.v56572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56572 s i)) at 1.
  unfold R.v56572, N.v56572.
  rewrite ?node_13286.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56573 (s : N.State) (i : N.Inputs) :
  R.v56573 (state s) (inputs i) = Zmod.unsigned (N.v56573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56573 s i)) at 1.
  unfold R.v56573, N.v56573.
  unfold R.v6, N.v6.
  rewrite ?node_13405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56574 (s : N.State) (i : N.Inputs) :
  R.v56574 (state s) (inputs i) = Zmod.unsigned (N.v56574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56574 s i)) at 1.
  unfold R.v56574, N.v56574.
  unfold R.v6, N.v6.
  rewrite ?node_13409.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56575 (s : N.State) (i : N.Inputs) :
  R.v56575 (state s) (inputs i) = Zmod.unsigned (N.v56575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56575 s i)) at 1.
  unfold R.v56575, N.v56575.
  rewrite ?node_56572.
  rewrite ?node_56573.
  rewrite ?node_56574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56576 (s : N.State) (i : N.Inputs) :
  R.v56576 (state s) (inputs i) = Zmod.unsigned (N.v56576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56576 s i)) at 1.
  unfold R.v56576, N.v56576.
  rewrite ?node_56571.
  rewrite ?node_56575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56577 (s : N.State) (i : N.Inputs) :
  R.v56577 (state s) (inputs i) = Zmod.unsigned (N.v56577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56577 s i)) at 1.
  unfold R.v56577, N.v56577.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56578 (s : N.State) (i : N.Inputs) :
  R.v56578 (state s) (inputs i) = Zmod.unsigned (N.v56578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56578 s i)) at 1.
  unfold R.v56578, N.v56578.
  rewrite ?node_13277.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56579 (s : N.State) (i : N.Inputs) :
  R.v56579 (state s) (inputs i) = Zmod.unsigned (N.v56579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56579 s i)) at 1.
  unfold R.v56579, N.v56579.
  unfold R.v6, N.v6.
  rewrite ?node_13273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56580 (s : N.State) (i : N.Inputs) :
  R.v56580 (state s) (inputs i) = Zmod.unsigned (N.v56580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56580 s i)) at 1.
  unfold R.v56580, N.v56580.
  unfold R.v6, N.v6.
  rewrite ?node_13266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56581 (s : N.State) (i : N.Inputs) :
  R.v56581 (state s) (inputs i) = Zmod.unsigned (N.v56581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56581 s i)) at 1.
  unfold R.v56581, N.v56581.
  rewrite ?node_56579.
  rewrite ?node_56580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56582 (s : N.State) (i : N.Inputs) :
  R.v56582 (state s) (inputs i) = Zmod.unsigned (N.v56582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56582 s i)) at 1.
  unfold R.v56582, N.v56582.
  unfold R.v16484, N.v16484.
  rewrite ?node_56581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56583 (s : N.State) (i : N.Inputs) :
  R.v56583 (state s) (inputs i) = Zmod.unsigned (N.v56583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56583 s i)) at 1.
  unfold R.v56583, N.v56583.
  rewrite ?node_56578.
  rewrite ?node_56582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56584 (s : N.State) (i : N.Inputs) :
  R.v56584 (state s) (inputs i) = Zmod.unsigned (N.v56584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56584 s i)) at 1.
  unfold R.v56584, N.v56584.
  unfold R.v6, N.v6.
  rewrite ?node_56583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56585 (s : N.State) (i : N.Inputs) :
  R.v56585 (state s) (inputs i) = Zmod.unsigned (N.v56585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56585 s i)) at 1.
  unfold R.v56585, N.v56585.
  rewrite ?node_13278.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56586 (s : N.State) (i : N.Inputs) :
  R.v56586 (state s) (inputs i) = Zmod.unsigned (N.v56586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56586 s i)) at 1.
  unfold R.v56586, N.v56586.
  unfold R.v6, N.v6.
  rewrite ?node_13405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56587 (s : N.State) (i : N.Inputs) :
  R.v56587 (state s) (inputs i) = Zmod.unsigned (N.v56587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56587 s i)) at 1.
  unfold R.v56587, N.v56587.
  rewrite ?node_56585.
  rewrite ?node_56586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56588 (s : N.State) (i : N.Inputs) :
  R.v56588 (state s) (inputs i) = Zmod.unsigned (N.v56588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56588 s i)) at 1.
  unfold R.v56588, N.v56588.
  rewrite ?node_56584.
  rewrite ?node_56587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56589 (s : N.State) (i : N.Inputs) :
  R.v56589 (state s) (inputs i) = Zmod.unsigned (N.v56589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56589 s i)) at 1.
  unfold R.v56589, N.v56589.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56590 (s : N.State) (i : N.Inputs) :
  R.v56590 (state s) (inputs i) = Zmod.unsigned (N.v56590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56590 s i)) at 1.
  unfold R.v56590, N.v56590.
  rewrite ?node_13285.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56591 (s : N.State) (i : N.Inputs) :
  R.v56591 (state s) (inputs i) = Zmod.unsigned (N.v56591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56591 s i)) at 1.
  unfold R.v56591, N.v56591.
  unfold R.v6, N.v6.
  rewrite ?node_13281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56592 (s : N.State) (i : N.Inputs) :
  R.v56592 (state s) (inputs i) = Zmod.unsigned (N.v56592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56592 s i)) at 1.
  unfold R.v56592, N.v56592.
  unfold R.v6, N.v6.
  rewrite ?node_13278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56593 (s : N.State) (i : N.Inputs) :
  R.v56593 (state s) (inputs i) = Zmod.unsigned (N.v56593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56593 s i)) at 1.
  unfold R.v56593, N.v56593.
  rewrite ?node_56591.
  rewrite ?node_56592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56594 (s : N.State) (i : N.Inputs) :
  R.v56594 (state s) (inputs i) = Zmod.unsigned (N.v56594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56594 s i)) at 1.
  unfold R.v56594, N.v56594.
  unfold R.v16484, N.v16484.
  rewrite ?node_56593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56595 (s : N.State) (i : N.Inputs) :
  R.v56595 (state s) (inputs i) = Zmod.unsigned (N.v56595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56595 s i)) at 1.
  unfold R.v56595, N.v56595.
  rewrite ?node_56590.
  rewrite ?node_56594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56596 (s : N.State) (i : N.Inputs) :
  R.v56596 (state s) (inputs i) = Zmod.unsigned (N.v56596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56596 s i)) at 1.
  unfold R.v56596, N.v56596.
  unfold R.v6, N.v6.
  rewrite ?node_56595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56597 (s : N.State) (i : N.Inputs) :
  R.v56597 (state s) (inputs i) = Zmod.unsigned (N.v56597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56597 s i)) at 1.
  unfold R.v56597, N.v56597.
  rewrite ?node_13286.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56598 (s : N.State) (i : N.Inputs) :
  R.v56598 (state s) (inputs i) = Zmod.unsigned (N.v56598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56598 s i)) at 1.
  unfold R.v56598, N.v56598.
  unfold R.v6, N.v6.
  rewrite ?node_13409.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56599 (s : N.State) (i : N.Inputs) :
  R.v56599 (state s) (inputs i) = Zmod.unsigned (N.v56599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56599 s i)) at 1.
  unfold R.v56599, N.v56599.
  rewrite ?node_56597.
  rewrite ?node_56598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56600 (s : N.State) (i : N.Inputs) :
  R.v56600 (state s) (inputs i) = Zmod.unsigned (N.v56600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56600 s i)) at 1.
  unfold R.v56600, N.v56600.
  rewrite ?node_56596.
  rewrite ?node_56599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56601 (s : N.State) (i : N.Inputs) :
  R.v56601 (state s) (inputs i) = Zmod.unsigned (N.v56601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56601 s i)) at 1.
  unfold R.v56601, N.v56601.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56602 (s : N.State) (i : N.Inputs) :
  R.v56602 (state s) (inputs i) = Zmod.unsigned (N.v56602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56602 s i)) at 1.
  unfold R.v56602, N.v56602.
  rewrite ?node_13405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56603 (s : N.State) (i : N.Inputs) :
  R.v56603 (state s) (inputs i) = Zmod.unsigned (N.v56603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56603 s i)) at 1.
  unfold R.v56603, N.v56603.
  rewrite ?node_13401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56604 (s : N.State) (i : N.Inputs) :
  R.v56604 (state s) (inputs i) = Zmod.unsigned (N.v56604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56604 s i)) at 1.
  unfold R.v56604, N.v56604.
  rewrite ?node_13399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56605 (s : N.State) (i : N.Inputs) :
  R.v56605 (state s) (inputs i) = Zmod.unsigned (N.v56605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56605 s i)) at 1.
  unfold R.v56605, N.v56605.
  unfold R.v6, N.v6.
  rewrite ?node_13395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56606 (s : N.State) (i : N.Inputs) :
  R.v56606 (state s) (inputs i) = Zmod.unsigned (N.v56606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56606 s i)) at 1.
  unfold R.v56606, N.v56606.
  unfold R.v6, N.v6.
  rewrite ?node_13388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56607 (s : N.State) (i : N.Inputs) :
  R.v56607 (state s) (inputs i) = Zmod.unsigned (N.v56607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56607 s i)) at 1.
  unfold R.v56607, N.v56607.
  rewrite ?node_56605.
  rewrite ?node_56606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56608 (s : N.State) (i : N.Inputs) :
  R.v56608 (state s) (inputs i) = Zmod.unsigned (N.v56608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56608 s i)) at 1.
  unfold R.v56608, N.v56608.
  unfold R.v16484, N.v16484.
  rewrite ?node_56607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56609 (s : N.State) (i : N.Inputs) :
  R.v56609 (state s) (inputs i) = Zmod.unsigned (N.v56609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56609 s i)) at 1.
  unfold R.v56609, N.v56609.
  rewrite ?node_56602.
  rewrite ?node_56603.
  rewrite ?node_56604.
  rewrite ?node_56608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56610 (s : N.State) (i : N.Inputs) :
  R.v56610 (state s) (inputs i) = Zmod.unsigned (N.v56610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56610 s i)) at 1.
  unfold R.v56610, N.v56610.
  unfold R.v6, N.v6.
  rewrite ?node_56609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56611 (s : N.State) (i : N.Inputs) :
  R.v56611 (state s) (inputs i) = Zmod.unsigned (N.v56611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56611 s i)) at 1.
  unfold R.v56611, N.v56611.
  rewrite ?node_13406.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56612 (s : N.State) (i : N.Inputs) :
  R.v56612 (state s) (inputs i) = Zmod.unsigned (N.v56612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56612 s i)) at 1.
  unfold R.v56612, N.v56612.
  unfold R.v6, N.v6.
  rewrite ?node_13521.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56613 (s : N.State) (i : N.Inputs) :
  R.v56613 (state s) (inputs i) = Zmod.unsigned (N.v56613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56613 s i)) at 1.
  unfold R.v56613, N.v56613.
  unfold R.v6, N.v6.
  rewrite ?node_13525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56614 (s : N.State) (i : N.Inputs) :
  R.v56614 (state s) (inputs i) = Zmod.unsigned (N.v56614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56614 s i)) at 1.
  unfold R.v56614, N.v56614.
  rewrite ?node_56611.
  rewrite ?node_56612.
  rewrite ?node_56613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56615 (s : N.State) (i : N.Inputs) :
  R.v56615 (state s) (inputs i) = Zmod.unsigned (N.v56615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56615 s i)) at 1.
  unfold R.v56615, N.v56615.
  rewrite ?node_56610.
  rewrite ?node_56614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56616 (s : N.State) (i : N.Inputs) :
  R.v56616 (state s) (inputs i) = Zmod.unsigned (N.v56616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56616 s i)) at 1.
  unfold R.v56616, N.v56616.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56617 (s : N.State) (i : N.Inputs) :
  R.v56617 (state s) (inputs i) = Zmod.unsigned (N.v56617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56617 s i)) at 1.
  unfold R.v56617, N.v56617.
  rewrite ?node_13399.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56618 (s : N.State) (i : N.Inputs) :
  R.v56618 (state s) (inputs i) = Zmod.unsigned (N.v56618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56618 s i)) at 1.
  unfold R.v56618, N.v56618.
  unfold R.v6, N.v6.
  rewrite ?node_13395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56619 (s : N.State) (i : N.Inputs) :
  R.v56619 (state s) (inputs i) = Zmod.unsigned (N.v56619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56619 s i)) at 1.
  unfold R.v56619, N.v56619.
  unfold R.v6, N.v6.
  rewrite ?node_13388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56620 (s : N.State) (i : N.Inputs) :
  R.v56620 (state s) (inputs i) = Zmod.unsigned (N.v56620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56620 s i)) at 1.
  unfold R.v56620, N.v56620.
  rewrite ?node_56618.
  rewrite ?node_56619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56621 (s : N.State) (i : N.Inputs) :
  R.v56621 (state s) (inputs i) = Zmod.unsigned (N.v56621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56621 s i)) at 1.
  unfold R.v56621, N.v56621.
  unfold R.v16484, N.v16484.
  rewrite ?node_56620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56622 (s : N.State) (i : N.Inputs) :
  R.v56622 (state s) (inputs i) = Zmod.unsigned (N.v56622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56622 s i)) at 1.
  unfold R.v56622, N.v56622.
  rewrite ?node_56617.
  rewrite ?node_56621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56623 (s : N.State) (i : N.Inputs) :
  R.v56623 (state s) (inputs i) = Zmod.unsigned (N.v56623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56623 s i)) at 1.
  unfold R.v56623, N.v56623.
  unfold R.v6, N.v6.
  rewrite ?node_56622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56624 (s : N.State) (i : N.Inputs) :
  R.v56624 (state s) (inputs i) = Zmod.unsigned (N.v56624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56624 s i)) at 1.
  unfold R.v56624, N.v56624.
  rewrite ?node_13400.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56625 (s : N.State) (i : N.Inputs) :
  R.v56625 (state s) (inputs i) = Zmod.unsigned (N.v56625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56625 s i)) at 1.
  unfold R.v56625, N.v56625.
  unfold R.v6, N.v6.
  rewrite ?node_13521.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56626 (s : N.State) (i : N.Inputs) :
  R.v56626 (state s) (inputs i) = Zmod.unsigned (N.v56626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56626 s i)) at 1.
  unfold R.v56626, N.v56626.
  rewrite ?node_56624.
  rewrite ?node_56625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56627 (s : N.State) (i : N.Inputs) :
  R.v56627 (state s) (inputs i) = Zmod.unsigned (N.v56627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56627 s i)) at 1.
  unfold R.v56627, N.v56627.
  rewrite ?node_56623.
  rewrite ?node_56626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56628 (s : N.State) (i : N.Inputs) :
  R.v56628 (state s) (inputs i) = Zmod.unsigned (N.v56628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56628 s i)) at 1.
  unfold R.v56628, N.v56628.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56629 (s : N.State) (i : N.Inputs) :
  R.v56629 (state s) (inputs i) = Zmod.unsigned (N.v56629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56629 s i)) at 1.
  unfold R.v56629, N.v56629.
  rewrite ?node_13405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56630 (s : N.State) (i : N.Inputs) :
  R.v56630 (state s) (inputs i) = Zmod.unsigned (N.v56630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56630 s i)) at 1.
  unfold R.v56630, N.v56630.
  unfold R.v6, N.v6.
  rewrite ?node_13401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56631 (s : N.State) (i : N.Inputs) :
  R.v56631 (state s) (inputs i) = Zmod.unsigned (N.v56631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56631 s i)) at 1.
  unfold R.v56631, N.v56631.
  unfold R.v6, N.v6.
  rewrite ?node_13400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56632 (s : N.State) (i : N.Inputs) :
  R.v56632 (state s) (inputs i) = Zmod.unsigned (N.v56632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56632 s i)) at 1.
  unfold R.v56632, N.v56632.
  rewrite ?node_56630.
  rewrite ?node_56631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56633 (s : N.State) (i : N.Inputs) :
  R.v56633 (state s) (inputs i) = Zmod.unsigned (N.v56633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56633 s i)) at 1.
  unfold R.v56633, N.v56633.
  unfold R.v16484, N.v16484.
  rewrite ?node_56632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56634 (s : N.State) (i : N.Inputs) :
  R.v56634 (state s) (inputs i) = Zmod.unsigned (N.v56634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56634 s i)) at 1.
  unfold R.v56634, N.v56634.
  rewrite ?node_56629.
  rewrite ?node_56633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56635 (s : N.State) (i : N.Inputs) :
  R.v56635 (state s) (inputs i) = Zmod.unsigned (N.v56635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56635 s i)) at 1.
  unfold R.v56635, N.v56635.
  unfold R.v6, N.v6.
  rewrite ?node_56634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56636 (s : N.State) (i : N.Inputs) :
  R.v56636 (state s) (inputs i) = Zmod.unsigned (N.v56636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56636 s i)) at 1.
  unfold R.v56636, N.v56636.
  rewrite ?node_13406.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56637 (s : N.State) (i : N.Inputs) :
  R.v56637 (state s) (inputs i) = Zmod.unsigned (N.v56637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56637 s i)) at 1.
  unfold R.v56637, N.v56637.
  unfold R.v6, N.v6.
  rewrite ?node_13525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56638 (s : N.State) (i : N.Inputs) :
  R.v56638 (state s) (inputs i) = Zmod.unsigned (N.v56638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56638 s i)) at 1.
  unfold R.v56638, N.v56638.
  rewrite ?node_56636.
  rewrite ?node_56637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56639 (s : N.State) (i : N.Inputs) :
  R.v56639 (state s) (inputs i) = Zmod.unsigned (N.v56639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56639 s i)) at 1.
  unfold R.v56639, N.v56639.
  rewrite ?node_56635.
  rewrite ?node_56638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56640 (s : N.State) (i : N.Inputs) :
  R.v56640 (state s) (inputs i) = Zmod.unsigned (N.v56640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56640 s i)) at 1.
  unfold R.v56640, N.v56640.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56641 (s : N.State) (i : N.Inputs) :
  R.v56641 (state s) (inputs i) = Zmod.unsigned (N.v56641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56641 s i)) at 1.
  unfold R.v56641, N.v56641.
  rewrite ?node_13521.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56642 (s : N.State) (i : N.Inputs) :
  R.v56642 (state s) (inputs i) = Zmod.unsigned (N.v56642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56642 s i)) at 1.
  unfold R.v56642, N.v56642.
  rewrite ?node_13517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56643 (s : N.State) (i : N.Inputs) :
  R.v56643 (state s) (inputs i) = Zmod.unsigned (N.v56643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56643 s i)) at 1.
  unfold R.v56643, N.v56643.
  rewrite ?node_13515.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56644 (s : N.State) (i : N.Inputs) :
  R.v56644 (state s) (inputs i) = Zmod.unsigned (N.v56644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56644 s i)) at 1.
  unfold R.v56644, N.v56644.
  unfold R.v6, N.v6.
  rewrite ?node_13511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56645 (s : N.State) (i : N.Inputs) :
  R.v56645 (state s) (inputs i) = Zmod.unsigned (N.v56645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56645 s i)) at 1.
  unfold R.v56645, N.v56645.
  unfold R.v6, N.v6.
  rewrite ?node_13500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56646 (s : N.State) (i : N.Inputs) :
  R.v56646 (state s) (inputs i) = Zmod.unsigned (N.v56646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56646 s i)) at 1.
  unfold R.v56646, N.v56646.
  rewrite ?node_56644.
  rewrite ?node_56645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56647 (s : N.State) (i : N.Inputs) :
  R.v56647 (state s) (inputs i) = Zmod.unsigned (N.v56647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56647 s i)) at 1.
  unfold R.v56647, N.v56647.
  unfold R.v16484, N.v16484.
  rewrite ?node_56646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56648 (s : N.State) (i : N.Inputs) :
  R.v56648 (state s) (inputs i) = Zmod.unsigned (N.v56648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56648 s i)) at 1.
  unfold R.v56648, N.v56648.
  rewrite ?node_56641.
  rewrite ?node_56642.
  rewrite ?node_56643.
  rewrite ?node_56647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56649 (s : N.State) (i : N.Inputs) :
  R.v56649 (state s) (inputs i) = Zmod.unsigned (N.v56649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56649 s i)) at 1.
  unfold R.v56649, N.v56649.
  unfold R.v6, N.v6.
  rewrite ?node_56648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56650 (s : N.State) (i : N.Inputs) :
  R.v56650 (state s) (inputs i) = Zmod.unsigned (N.v56650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56650 s i)) at 1.
  unfold R.v56650, N.v56650.
  rewrite ?node_13522.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56651 (s : N.State) (i : N.Inputs) :
  R.v56651 (state s) (inputs i) = Zmod.unsigned (N.v56651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56651 s i)) at 1.
  unfold R.v56651, N.v56651.
  unfold R.v6, N.v6.
  rewrite ?node_13634.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56652 (s : N.State) (i : N.Inputs) :
  R.v56652 (state s) (inputs i) = Zmod.unsigned (N.v56652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56652 s i)) at 1.
  unfold R.v56652, N.v56652.
  unfold R.v6, N.v6.
  rewrite ?node_13638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56653 (s : N.State) (i : N.Inputs) :
  R.v56653 (state s) (inputs i) = Zmod.unsigned (N.v56653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56653 s i)) at 1.
  unfold R.v56653, N.v56653.
  rewrite ?node_56650.
  rewrite ?node_56651.
  rewrite ?node_56652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56654 (s : N.State) (i : N.Inputs) :
  R.v56654 (state s) (inputs i) = Zmod.unsigned (N.v56654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56654 s i)) at 1.
  unfold R.v56654, N.v56654.
  rewrite ?node_56649.
  rewrite ?node_56653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56655 (s : N.State) (i : N.Inputs) :
  R.v56655 (state s) (inputs i) = Zmod.unsigned (N.v56655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56655 s i)) at 1.
  unfold R.v56655, N.v56655.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56656 (s : N.State) (i : N.Inputs) :
  R.v56656 (state s) (inputs i) = Zmod.unsigned (N.v56656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56656 s i)) at 1.
  unfold R.v56656, N.v56656.
  rewrite ?node_13515.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56657 (s : N.State) (i : N.Inputs) :
  R.v56657 (state s) (inputs i) = Zmod.unsigned (N.v56657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56657 s i)) at 1.
  unfold R.v56657, N.v56657.
  unfold R.v6, N.v6.
  rewrite ?node_13511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56658 (s : N.State) (i : N.Inputs) :
  R.v56658 (state s) (inputs i) = Zmod.unsigned (N.v56658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56658 s i)) at 1.
  unfold R.v56658, N.v56658.
  unfold R.v6, N.v6.
  rewrite ?node_13500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56659 (s : N.State) (i : N.Inputs) :
  R.v56659 (state s) (inputs i) = Zmod.unsigned (N.v56659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56659 s i)) at 1.
  unfold R.v56659, N.v56659.
  rewrite ?node_56657.
  rewrite ?node_56658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56660 (s : N.State) (i : N.Inputs) :
  R.v56660 (state s) (inputs i) = Zmod.unsigned (N.v56660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56660 s i)) at 1.
  unfold R.v56660, N.v56660.
  unfold R.v16484, N.v16484.
  rewrite ?node_56659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56661 (s : N.State) (i : N.Inputs) :
  R.v56661 (state s) (inputs i) = Zmod.unsigned (N.v56661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56661 s i)) at 1.
  unfold R.v56661, N.v56661.
  rewrite ?node_56656.
  rewrite ?node_56660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56662 (s : N.State) (i : N.Inputs) :
  R.v56662 (state s) (inputs i) = Zmod.unsigned (N.v56662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56662 s i)) at 1.
  unfold R.v56662, N.v56662.
  unfold R.v6, N.v6.
  rewrite ?node_56661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56663 (s : N.State) (i : N.Inputs) :
  R.v56663 (state s) (inputs i) = Zmod.unsigned (N.v56663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56663 s i)) at 1.
  unfold R.v56663, N.v56663.
  rewrite ?node_13516.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56664 (s : N.State) (i : N.Inputs) :
  R.v56664 (state s) (inputs i) = Zmod.unsigned (N.v56664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56664 s i)) at 1.
  unfold R.v56664, N.v56664.
  unfold R.v6, N.v6.
  rewrite ?node_13634.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56665 (s : N.State) (i : N.Inputs) :
  R.v56665 (state s) (inputs i) = Zmod.unsigned (N.v56665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56665 s i)) at 1.
  unfold R.v56665, N.v56665.
  rewrite ?node_56663.
  rewrite ?node_56664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56666 (s : N.State) (i : N.Inputs) :
  R.v56666 (state s) (inputs i) = Zmod.unsigned (N.v56666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56666 s i)) at 1.
  unfold R.v56666, N.v56666.
  rewrite ?node_56662.
  rewrite ?node_56665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56667 (s : N.State) (i : N.Inputs) :
  R.v56667 (state s) (inputs i) = Zmod.unsigned (N.v56667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56667 s i)) at 1.
  unfold R.v56667, N.v56667.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56668 (s : N.State) (i : N.Inputs) :
  R.v56668 (state s) (inputs i) = Zmod.unsigned (N.v56668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56668 s i)) at 1.
  unfold R.v56668, N.v56668.
  rewrite ?node_13521.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56669 (s : N.State) (i : N.Inputs) :
  R.v56669 (state s) (inputs i) = Zmod.unsigned (N.v56669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56669 s i)) at 1.
  unfold R.v56669, N.v56669.
  unfold R.v6, N.v6.
  rewrite ?node_13517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56670 (s : N.State) (i : N.Inputs) :
  R.v56670 (state s) (inputs i) = Zmod.unsigned (N.v56670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56670 s i)) at 1.
  unfold R.v56670, N.v56670.
  unfold R.v6, N.v6.
  rewrite ?node_13516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56671 (s : N.State) (i : N.Inputs) :
  R.v56671 (state s) (inputs i) = Zmod.unsigned (N.v56671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56671 s i)) at 1.
  unfold R.v56671, N.v56671.
  rewrite ?node_56669.
  rewrite ?node_56670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56672 (s : N.State) (i : N.Inputs) :
  R.v56672 (state s) (inputs i) = Zmod.unsigned (N.v56672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56672 s i)) at 1.
  unfold R.v56672, N.v56672.
  unfold R.v16484, N.v16484.
  rewrite ?node_56671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56673 (s : N.State) (i : N.Inputs) :
  R.v56673 (state s) (inputs i) = Zmod.unsigned (N.v56673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56673 s i)) at 1.
  unfold R.v56673, N.v56673.
  rewrite ?node_56668.
  rewrite ?node_56672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56674 (s : N.State) (i : N.Inputs) :
  R.v56674 (state s) (inputs i) = Zmod.unsigned (N.v56674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56674 s i)) at 1.
  unfold R.v56674, N.v56674.
  unfold R.v6, N.v6.
  rewrite ?node_56673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56675 (s : N.State) (i : N.Inputs) :
  R.v56675 (state s) (inputs i) = Zmod.unsigned (N.v56675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56675 s i)) at 1.
  unfold R.v56675, N.v56675.
  rewrite ?node_13522.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56676 (s : N.State) (i : N.Inputs) :
  R.v56676 (state s) (inputs i) = Zmod.unsigned (N.v56676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56676 s i)) at 1.
  unfold R.v56676, N.v56676.
  unfold R.v6, N.v6.
  rewrite ?node_13638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56677 (s : N.State) (i : N.Inputs) :
  R.v56677 (state s) (inputs i) = Zmod.unsigned (N.v56677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56677 s i)) at 1.
  unfold R.v56677, N.v56677.
  rewrite ?node_56675.
  rewrite ?node_56676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56678 (s : N.State) (i : N.Inputs) :
  R.v56678 (state s) (inputs i) = Zmod.unsigned (N.v56678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56678 s i)) at 1.
  unfold R.v56678, N.v56678.
  rewrite ?node_56674.
  rewrite ?node_56677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56679 (s : N.State) (i : N.Inputs) :
  R.v56679 (state s) (inputs i) = Zmod.unsigned (N.v56679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56679 s i)) at 1.
  unfold R.v56679, N.v56679.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56680 (s : N.State) (i : N.Inputs) :
  R.v56680 (state s) (inputs i) = Zmod.unsigned (N.v56680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56680 s i)) at 1.
  unfold R.v56680, N.v56680.
  rewrite ?node_13634.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56681 (s : N.State) (i : N.Inputs) :
  R.v56681 (state s) (inputs i) = Zmod.unsigned (N.v56681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56681 s i)) at 1.
  unfold R.v56681, N.v56681.
  rewrite ?node_13630.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56682 (s : N.State) (i : N.Inputs) :
  R.v56682 (state s) (inputs i) = Zmod.unsigned (N.v56682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56682 s i)) at 1.
  unfold R.v56682, N.v56682.
  rewrite ?node_13626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56683 (s : N.State) (i : N.Inputs) :
  R.v56683 (state s) (inputs i) = Zmod.unsigned (N.v56683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56683 s i)) at 1.
  unfold R.v56683, N.v56683.
  unfold R.v6, N.v6.
  rewrite ?node_13622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56684 (s : N.State) (i : N.Inputs) :
  R.v56684 (state s) (inputs i) = Zmod.unsigned (N.v56684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56684 s i)) at 1.
  unfold R.v56684, N.v56684.
  unfold R.v6, N.v6.
  rewrite ?node_13615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56685 (s : N.State) (i : N.Inputs) :
  R.v56685 (state s) (inputs i) = Zmod.unsigned (N.v56685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56685 s i)) at 1.
  unfold R.v56685, N.v56685.
  rewrite ?node_56683.
  rewrite ?node_56684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56686 (s : N.State) (i : N.Inputs) :
  R.v56686 (state s) (inputs i) = Zmod.unsigned (N.v56686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56686 s i)) at 1.
  unfold R.v56686, N.v56686.
  unfold R.v16484, N.v16484.
  rewrite ?node_56685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56687 (s : N.State) (i : N.Inputs) :
  R.v56687 (state s) (inputs i) = Zmod.unsigned (N.v56687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56687 s i)) at 1.
  unfold R.v56687, N.v56687.
  rewrite ?node_56680.
  rewrite ?node_56681.
  rewrite ?node_56682.
  rewrite ?node_56686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56688 (s : N.State) (i : N.Inputs) :
  R.v56688 (state s) (inputs i) = Zmod.unsigned (N.v56688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56688 s i)) at 1.
  unfold R.v56688, N.v56688.
  unfold R.v6, N.v6.
  rewrite ?node_56687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56689 (s : N.State) (i : N.Inputs) :
  R.v56689 (state s) (inputs i) = Zmod.unsigned (N.v56689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56689 s i)) at 1.
  unfold R.v56689, N.v56689.
  rewrite ?node_13635.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56690 (s : N.State) (i : N.Inputs) :
  R.v56690 (state s) (inputs i) = Zmod.unsigned (N.v56690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56690 s i)) at 1.
  unfold R.v56690, N.v56690.
  unfold R.v6, N.v6.
  rewrite ?node_13743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56691 (s : N.State) (i : N.Inputs) :
  R.v56691 (state s) (inputs i) = Zmod.unsigned (N.v56691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56691 s i)) at 1.
  unfold R.v56691, N.v56691.
  unfold R.v6, N.v6.
  rewrite ?node_13747.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56692 (s : N.State) (i : N.Inputs) :
  R.v56692 (state s) (inputs i) = Zmod.unsigned (N.v56692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56692 s i)) at 1.
  unfold R.v56692, N.v56692.
  rewrite ?node_56689.
  rewrite ?node_56690.
  rewrite ?node_56691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56693 (s : N.State) (i : N.Inputs) :
  R.v56693 (state s) (inputs i) = Zmod.unsigned (N.v56693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56693 s i)) at 1.
  unfold R.v56693, N.v56693.
  rewrite ?node_56688.
  rewrite ?node_56692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56694 (s : N.State) (i : N.Inputs) :
  R.v56694 (state s) (inputs i) = Zmod.unsigned (N.v56694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56694 s i)) at 1.
  unfold R.v56694, N.v56694.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56695 (s : N.State) (i : N.Inputs) :
  R.v56695 (state s) (inputs i) = Zmod.unsigned (N.v56695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56695 s i)) at 1.
  unfold R.v56695, N.v56695.
  rewrite ?node_13626.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56696 (s : N.State) (i : N.Inputs) :
  R.v56696 (state s) (inputs i) = Zmod.unsigned (N.v56696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56696 s i)) at 1.
  unfold R.v56696, N.v56696.
  unfold R.v6, N.v6.
  rewrite ?node_13622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56697 (s : N.State) (i : N.Inputs) :
  R.v56697 (state s) (inputs i) = Zmod.unsigned (N.v56697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56697 s i)) at 1.
  unfold R.v56697, N.v56697.
  unfold R.v6, N.v6.
  rewrite ?node_13615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56698 (s : N.State) (i : N.Inputs) :
  R.v56698 (state s) (inputs i) = Zmod.unsigned (N.v56698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56698 s i)) at 1.
  unfold R.v56698, N.v56698.
  rewrite ?node_56696.
  rewrite ?node_56697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56699 (s : N.State) (i : N.Inputs) :
  R.v56699 (state s) (inputs i) = Zmod.unsigned (N.v56699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56699 s i)) at 1.
  unfold R.v56699, N.v56699.
  unfold R.v16484, N.v16484.
  rewrite ?node_56698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56700 (s : N.State) (i : N.Inputs) :
  R.v56700 (state s) (inputs i) = Zmod.unsigned (N.v56700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56700 s i)) at 1.
  unfold R.v56700, N.v56700.
  rewrite ?node_56695.
  rewrite ?node_56699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56701 (s : N.State) (i : N.Inputs) :
  R.v56701 (state s) (inputs i) = Zmod.unsigned (N.v56701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56701 s i)) at 1.
  unfold R.v56701, N.v56701.
  unfold R.v6, N.v6.
  rewrite ?node_56700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56702 (s : N.State) (i : N.Inputs) :
  R.v56702 (state s) (inputs i) = Zmod.unsigned (N.v56702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56702 s i)) at 1.
  unfold R.v56702, N.v56702.
  rewrite ?node_13627.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56703 (s : N.State) (i : N.Inputs) :
  R.v56703 (state s) (inputs i) = Zmod.unsigned (N.v56703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56703 s i)) at 1.
  unfold R.v56703, N.v56703.
  unfold R.v6, N.v6.
  rewrite ?node_13743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56704 (s : N.State) (i : N.Inputs) :
  R.v56704 (state s) (inputs i) = Zmod.unsigned (N.v56704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56704 s i)) at 1.
  unfold R.v56704, N.v56704.
  rewrite ?node_56702.
  rewrite ?node_56703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56705 (s : N.State) (i : N.Inputs) :
  R.v56705 (state s) (inputs i) = Zmod.unsigned (N.v56705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56705 s i)) at 1.
  unfold R.v56705, N.v56705.
  rewrite ?node_56701.
  rewrite ?node_56704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56706 (s : N.State) (i : N.Inputs) :
  R.v56706 (state s) (inputs i) = Zmod.unsigned (N.v56706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56706 s i)) at 1.
  unfold R.v56706, N.v56706.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56707 (s : N.State) (i : N.Inputs) :
  R.v56707 (state s) (inputs i) = Zmod.unsigned (N.v56707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56707 s i)) at 1.
  unfold R.v56707, N.v56707.
  rewrite ?node_13634.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56708 (s : N.State) (i : N.Inputs) :
  R.v56708 (state s) (inputs i) = Zmod.unsigned (N.v56708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56708 s i)) at 1.
  unfold R.v56708, N.v56708.
  unfold R.v6, N.v6.
  rewrite ?node_13630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56709 (s : N.State) (i : N.Inputs) :
  R.v56709 (state s) (inputs i) = Zmod.unsigned (N.v56709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56709 s i)) at 1.
  unfold R.v56709, N.v56709.
  unfold R.v6, N.v6.
  rewrite ?node_13627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56710 (s : N.State) (i : N.Inputs) :
  R.v56710 (state s) (inputs i) = Zmod.unsigned (N.v56710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56710 s i)) at 1.
  unfold R.v56710, N.v56710.
  rewrite ?node_56708.
  rewrite ?node_56709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56711 (s : N.State) (i : N.Inputs) :
  R.v56711 (state s) (inputs i) = Zmod.unsigned (N.v56711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56711 s i)) at 1.
  unfold R.v56711, N.v56711.
  unfold R.v16484, N.v16484.
  rewrite ?node_56710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56712 (s : N.State) (i : N.Inputs) :
  R.v56712 (state s) (inputs i) = Zmod.unsigned (N.v56712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56712 s i)) at 1.
  unfold R.v56712, N.v56712.
  rewrite ?node_56707.
  rewrite ?node_56711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56713 (s : N.State) (i : N.Inputs) :
  R.v56713 (state s) (inputs i) = Zmod.unsigned (N.v56713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56713 s i)) at 1.
  unfold R.v56713, N.v56713.
  unfold R.v6, N.v6.
  rewrite ?node_56712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56714 (s : N.State) (i : N.Inputs) :
  R.v56714 (state s) (inputs i) = Zmod.unsigned (N.v56714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56714 s i)) at 1.
  unfold R.v56714, N.v56714.
  rewrite ?node_13635.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56715 (s : N.State) (i : N.Inputs) :
  R.v56715 (state s) (inputs i) = Zmod.unsigned (N.v56715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56715 s i)) at 1.
  unfold R.v56715, N.v56715.
  unfold R.v6, N.v6.
  rewrite ?node_13747.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56716 (s : N.State) (i : N.Inputs) :
  R.v56716 (state s) (inputs i) = Zmod.unsigned (N.v56716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56716 s i)) at 1.
  unfold R.v56716, N.v56716.
  rewrite ?node_56714.
  rewrite ?node_56715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56717 (s : N.State) (i : N.Inputs) :
  R.v56717 (state s) (inputs i) = Zmod.unsigned (N.v56717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56717 s i)) at 1.
  unfold R.v56717, N.v56717.
  rewrite ?node_56713.
  rewrite ?node_56716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56718 (s : N.State) (i : N.Inputs) :
  R.v56718 (state s) (inputs i) = Zmod.unsigned (N.v56718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56718 s i)) at 1.
  unfold R.v56718, N.v56718.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56719 (s : N.State) (i : N.Inputs) :
  R.v56719 (state s) (inputs i) = Zmod.unsigned (N.v56719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56719 s i)) at 1.
  unfold R.v56719, N.v56719.
  rewrite ?node_13743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56720 (s : N.State) (i : N.Inputs) :
  R.v56720 (state s) (inputs i) = Zmod.unsigned (N.v56720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56720 s i)) at 1.
  unfold R.v56720, N.v56720.
  rewrite ?node_13739.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56721 (s : N.State) (i : N.Inputs) :
  R.v56721 (state s) (inputs i) = Zmod.unsigned (N.v56721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56721 s i)) at 1.
  unfold R.v56721, N.v56721.
  rewrite ?node_13737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56722 (s : N.State) (i : N.Inputs) :
  R.v56722 (state s) (inputs i) = Zmod.unsigned (N.v56722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56722 s i)) at 1.
  unfold R.v56722, N.v56722.
  unfold R.v6, N.v6.
  rewrite ?node_13733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56723 (s : N.State) (i : N.Inputs) :
  R.v56723 (state s) (inputs i) = Zmod.unsigned (N.v56723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56723 s i)) at 1.
  unfold R.v56723, N.v56723.
  unfold R.v6, N.v6.
  rewrite ?node_13726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56724 (s : N.State) (i : N.Inputs) :
  R.v56724 (state s) (inputs i) = Zmod.unsigned (N.v56724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56724 s i)) at 1.
  unfold R.v56724, N.v56724.
  rewrite ?node_56722.
  rewrite ?node_56723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56725 (s : N.State) (i : N.Inputs) :
  R.v56725 (state s) (inputs i) = Zmod.unsigned (N.v56725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56725 s i)) at 1.
  unfold R.v56725, N.v56725.
  unfold R.v16484, N.v16484.
  rewrite ?node_56724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56726 (s : N.State) (i : N.Inputs) :
  R.v56726 (state s) (inputs i) = Zmod.unsigned (N.v56726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56726 s i)) at 1.
  unfold R.v56726, N.v56726.
  rewrite ?node_56719.
  rewrite ?node_56720.
  rewrite ?node_56721.
  rewrite ?node_56725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56727 (s : N.State) (i : N.Inputs) :
  R.v56727 (state s) (inputs i) = Zmod.unsigned (N.v56727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56727 s i)) at 1.
  unfold R.v56727, N.v56727.
  unfold R.v6, N.v6.
  rewrite ?node_56726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56728 (s : N.State) (i : N.Inputs) :
  R.v56728 (state s) (inputs i) = Zmod.unsigned (N.v56728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56728 s i)) at 1.
  unfold R.v56728, N.v56728.
  rewrite ?node_13744.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56729 (s : N.State) (i : N.Inputs) :
  R.v56729 (state s) (inputs i) = Zmod.unsigned (N.v56729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56729 s i)) at 1.
  unfold R.v56729, N.v56729.
  unfold R.v6, N.v6.
  rewrite ?node_13851.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56730 (s : N.State) (i : N.Inputs) :
  R.v56730 (state s) (inputs i) = Zmod.unsigned (N.v56730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56730 s i)) at 1.
  unfold R.v56730, N.v56730.
  unfold R.v6, N.v6.
  rewrite ?node_13855.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56731 (s : N.State) (i : N.Inputs) :
  R.v56731 (state s) (inputs i) = Zmod.unsigned (N.v56731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56731 s i)) at 1.
  unfold R.v56731, N.v56731.
  rewrite ?node_56728.
  rewrite ?node_56729.
  rewrite ?node_56730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56732 (s : N.State) (i : N.Inputs) :
  R.v56732 (state s) (inputs i) = Zmod.unsigned (N.v56732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56732 s i)) at 1.
  unfold R.v56732, N.v56732.
  rewrite ?node_56727.
  rewrite ?node_56731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56733 (s : N.State) (i : N.Inputs) :
  R.v56733 (state s) (inputs i) = Zmod.unsigned (N.v56733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56733 s i)) at 1.
  unfold R.v56733, N.v56733.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56734 (s : N.State) (i : N.Inputs) :
  R.v56734 (state s) (inputs i) = Zmod.unsigned (N.v56734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56734 s i)) at 1.
  unfold R.v56734, N.v56734.
  rewrite ?node_13737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56735 (s : N.State) (i : N.Inputs) :
  R.v56735 (state s) (inputs i) = Zmod.unsigned (N.v56735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56735 s i)) at 1.
  unfold R.v56735, N.v56735.
  unfold R.v6, N.v6.
  rewrite ?node_13733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56736 (s : N.State) (i : N.Inputs) :
  R.v56736 (state s) (inputs i) = Zmod.unsigned (N.v56736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56736 s i)) at 1.
  unfold R.v56736, N.v56736.
  unfold R.v6, N.v6.
  rewrite ?node_13726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56737 (s : N.State) (i : N.Inputs) :
  R.v56737 (state s) (inputs i) = Zmod.unsigned (N.v56737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56737 s i)) at 1.
  unfold R.v56737, N.v56737.
  rewrite ?node_56735.
  rewrite ?node_56736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56738 (s : N.State) (i : N.Inputs) :
  R.v56738 (state s) (inputs i) = Zmod.unsigned (N.v56738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56738 s i)) at 1.
  unfold R.v56738, N.v56738.
  unfold R.v16484, N.v16484.
  rewrite ?node_56737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56739 (s : N.State) (i : N.Inputs) :
  R.v56739 (state s) (inputs i) = Zmod.unsigned (N.v56739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56739 s i)) at 1.
  unfold R.v56739, N.v56739.
  rewrite ?node_56734.
  rewrite ?node_56738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56740 (s : N.State) (i : N.Inputs) :
  R.v56740 (state s) (inputs i) = Zmod.unsigned (N.v56740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56740 s i)) at 1.
  unfold R.v56740, N.v56740.
  unfold R.v6, N.v6.
  rewrite ?node_56739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56741 (s : N.State) (i : N.Inputs) :
  R.v56741 (state s) (inputs i) = Zmod.unsigned (N.v56741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56741 s i)) at 1.
  unfold R.v56741, N.v56741.
  rewrite ?node_13738.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56742 (s : N.State) (i : N.Inputs) :
  R.v56742 (state s) (inputs i) = Zmod.unsigned (N.v56742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56742 s i)) at 1.
  unfold R.v56742, N.v56742.
  unfold R.v6, N.v6.
  rewrite ?node_13851.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56743 (s : N.State) (i : N.Inputs) :
  R.v56743 (state s) (inputs i) = Zmod.unsigned (N.v56743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56743 s i)) at 1.
  unfold R.v56743, N.v56743.
  rewrite ?node_56741.
  rewrite ?node_56742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56744 (s : N.State) (i : N.Inputs) :
  R.v56744 (state s) (inputs i) = Zmod.unsigned (N.v56744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56744 s i)) at 1.
  unfold R.v56744, N.v56744.
  rewrite ?node_56740.
  rewrite ?node_56743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56745 (s : N.State) (i : N.Inputs) :
  R.v56745 (state s) (inputs i) = Zmod.unsigned (N.v56745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56745 s i)) at 1.
  unfold R.v56745, N.v56745.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56746 (s : N.State) (i : N.Inputs) :
  R.v56746 (state s) (inputs i) = Zmod.unsigned (N.v56746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56746 s i)) at 1.
  unfold R.v56746, N.v56746.
  rewrite ?node_13743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56747 (s : N.State) (i : N.Inputs) :
  R.v56747 (state s) (inputs i) = Zmod.unsigned (N.v56747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56747 s i)) at 1.
  unfold R.v56747, N.v56747.
  unfold R.v6, N.v6.
  rewrite ?node_13739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56748 (s : N.State) (i : N.Inputs) :
  R.v56748 (state s) (inputs i) = Zmod.unsigned (N.v56748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56748 s i)) at 1.
  unfold R.v56748, N.v56748.
  unfold R.v6, N.v6.
  rewrite ?node_13738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56749 (s : N.State) (i : N.Inputs) :
  R.v56749 (state s) (inputs i) = Zmod.unsigned (N.v56749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56749 s i)) at 1.
  unfold R.v56749, N.v56749.
  rewrite ?node_56747.
  rewrite ?node_56748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56750 (s : N.State) (i : N.Inputs) :
  R.v56750 (state s) (inputs i) = Zmod.unsigned (N.v56750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56750 s i)) at 1.
  unfold R.v56750, N.v56750.
  unfold R.v16484, N.v16484.
  rewrite ?node_56749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56751 (s : N.State) (i : N.Inputs) :
  R.v56751 (state s) (inputs i) = Zmod.unsigned (N.v56751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56751 s i)) at 1.
  unfold R.v56751, N.v56751.
  rewrite ?node_56746.
  rewrite ?node_56750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56752 (s : N.State) (i : N.Inputs) :
  R.v56752 (state s) (inputs i) = Zmod.unsigned (N.v56752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56752 s i)) at 1.
  unfold R.v56752, N.v56752.
  unfold R.v6, N.v6.
  rewrite ?node_56751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56753 (s : N.State) (i : N.Inputs) :
  R.v56753 (state s) (inputs i) = Zmod.unsigned (N.v56753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56753 s i)) at 1.
  unfold R.v56753, N.v56753.
  rewrite ?node_13744.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56754 (s : N.State) (i : N.Inputs) :
  R.v56754 (state s) (inputs i) = Zmod.unsigned (N.v56754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56754 s i)) at 1.
  unfold R.v56754, N.v56754.
  unfold R.v6, N.v6.
  rewrite ?node_13855.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56755 (s : N.State) (i : N.Inputs) :
  R.v56755 (state s) (inputs i) = Zmod.unsigned (N.v56755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56755 s i)) at 1.
  unfold R.v56755, N.v56755.
  rewrite ?node_56753.
  rewrite ?node_56754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56756 (s : N.State) (i : N.Inputs) :
  R.v56756 (state s) (inputs i) = Zmod.unsigned (N.v56756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56756 s i)) at 1.
  unfold R.v56756, N.v56756.
  rewrite ?node_56752.
  rewrite ?node_56755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56757 (s : N.State) (i : N.Inputs) :
  R.v56757 (state s) (inputs i) = Zmod.unsigned (N.v56757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56757 s i)) at 1.
  unfold R.v56757, N.v56757.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56758 (s : N.State) (i : N.Inputs) :
  R.v56758 (state s) (inputs i) = Zmod.unsigned (N.v56758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56758 s i)) at 1.
  unfold R.v56758, N.v56758.
  rewrite ?node_13851.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56759 (s : N.State) (i : N.Inputs) :
  R.v56759 (state s) (inputs i) = Zmod.unsigned (N.v56759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56759 s i)) at 1.
  unfold R.v56759, N.v56759.
  rewrite ?node_13847.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56760 (s : N.State) (i : N.Inputs) :
  R.v56760 (state s) (inputs i) = Zmod.unsigned (N.v56760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56760 s i)) at 1.
  unfold R.v56760, N.v56760.
  rewrite ?node_13845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56761 (s : N.State) (i : N.Inputs) :
  R.v56761 (state s) (inputs i) = Zmod.unsigned (N.v56761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56761 s i)) at 1.
  unfold R.v56761, N.v56761.
  unfold R.v6, N.v6.
  rewrite ?node_13841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56762 (s : N.State) (i : N.Inputs) :
  R.v56762 (state s) (inputs i) = Zmod.unsigned (N.v56762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56762 s i)) at 1.
  unfold R.v56762, N.v56762.
  unfold R.v6, N.v6.
  rewrite ?node_13834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56763 (s : N.State) (i : N.Inputs) :
  R.v56763 (state s) (inputs i) = Zmod.unsigned (N.v56763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56763 s i)) at 1.
  unfold R.v56763, N.v56763.
  rewrite ?node_56761.
  rewrite ?node_56762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56764 (s : N.State) (i : N.Inputs) :
  R.v56764 (state s) (inputs i) = Zmod.unsigned (N.v56764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56764 s i)) at 1.
  unfold R.v56764, N.v56764.
  unfold R.v16484, N.v16484.
  rewrite ?node_56763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56765 (s : N.State) (i : N.Inputs) :
  R.v56765 (state s) (inputs i) = Zmod.unsigned (N.v56765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56765 s i)) at 1.
  unfold R.v56765, N.v56765.
  rewrite ?node_56758.
  rewrite ?node_56759.
  rewrite ?node_56760.
  rewrite ?node_56764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56766 (s : N.State) (i : N.Inputs) :
  R.v56766 (state s) (inputs i) = Zmod.unsigned (N.v56766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56766 s i)) at 1.
  unfold R.v56766, N.v56766.
  unfold R.v6, N.v6.
  rewrite ?node_56765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56767 (s : N.State) (i : N.Inputs) :
  R.v56767 (state s) (inputs i) = Zmod.unsigned (N.v56767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56767 s i)) at 1.
  unfold R.v56767, N.v56767.
  rewrite ?node_13852.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56768 (s : N.State) (i : N.Inputs) :
  R.v56768 (state s) (inputs i) = Zmod.unsigned (N.v56768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56768 s i)) at 1.
  unfold R.v56768, N.v56768.
  unfold R.v6, N.v6.
  rewrite ?node_13957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56769 (s : N.State) (i : N.Inputs) :
  R.v56769 (state s) (inputs i) = Zmod.unsigned (N.v56769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56769 s i)) at 1.
  unfold R.v56769, N.v56769.
  unfold R.v6, N.v6.
  rewrite ?node_13961.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56770 (s : N.State) (i : N.Inputs) :
  R.v56770 (state s) (inputs i) = Zmod.unsigned (N.v56770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56770 s i)) at 1.
  unfold R.v56770, N.v56770.
  rewrite ?node_56767.
  rewrite ?node_56768.
  rewrite ?node_56769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56771 (s : N.State) (i : N.Inputs) :
  R.v56771 (state s) (inputs i) = Zmod.unsigned (N.v56771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56771 s i)) at 1.
  unfold R.v56771, N.v56771.
  rewrite ?node_56766.
  rewrite ?node_56770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56772 (s : N.State) (i : N.Inputs) :
  R.v56772 (state s) (inputs i) = Zmod.unsigned (N.v56772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56772 s i)) at 1.
  unfold R.v56772, N.v56772.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56773 (s : N.State) (i : N.Inputs) :
  R.v56773 (state s) (inputs i) = Zmod.unsigned (N.v56773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56773 s i)) at 1.
  unfold R.v56773, N.v56773.
  rewrite ?node_13845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56774 (s : N.State) (i : N.Inputs) :
  R.v56774 (state s) (inputs i) = Zmod.unsigned (N.v56774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56774 s i)) at 1.
  unfold R.v56774, N.v56774.
  unfold R.v6, N.v6.
  rewrite ?node_13841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56775 (s : N.State) (i : N.Inputs) :
  R.v56775 (state s) (inputs i) = Zmod.unsigned (N.v56775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56775 s i)) at 1.
  unfold R.v56775, N.v56775.
  unfold R.v6, N.v6.
  rewrite ?node_13834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56776 (s : N.State) (i : N.Inputs) :
  R.v56776 (state s) (inputs i) = Zmod.unsigned (N.v56776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56776 s i)) at 1.
  unfold R.v56776, N.v56776.
  rewrite ?node_56774.
  rewrite ?node_56775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56777 (s : N.State) (i : N.Inputs) :
  R.v56777 (state s) (inputs i) = Zmod.unsigned (N.v56777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56777 s i)) at 1.
  unfold R.v56777, N.v56777.
  unfold R.v16484, N.v16484.
  rewrite ?node_56776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56778 (s : N.State) (i : N.Inputs) :
  R.v56778 (state s) (inputs i) = Zmod.unsigned (N.v56778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56778 s i)) at 1.
  unfold R.v56778, N.v56778.
  rewrite ?node_56773.
  rewrite ?node_56777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56779 (s : N.State) (i : N.Inputs) :
  R.v56779 (state s) (inputs i) = Zmod.unsigned (N.v56779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56779 s i)) at 1.
  unfold R.v56779, N.v56779.
  unfold R.v6, N.v6.
  rewrite ?node_56778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56780 (s : N.State) (i : N.Inputs) :
  R.v56780 (state s) (inputs i) = Zmod.unsigned (N.v56780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56780 s i)) at 1.
  unfold R.v56780, N.v56780.
  rewrite ?node_13846.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56781 (s : N.State) (i : N.Inputs) :
  R.v56781 (state s) (inputs i) = Zmod.unsigned (N.v56781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56781 s i)) at 1.
  unfold R.v56781, N.v56781.
  unfold R.v6, N.v6.
  rewrite ?node_13957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56782 (s : N.State) (i : N.Inputs) :
  R.v56782 (state s) (inputs i) = Zmod.unsigned (N.v56782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56782 s i)) at 1.
  unfold R.v56782, N.v56782.
  rewrite ?node_56780.
  rewrite ?node_56781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56783 (s : N.State) (i : N.Inputs) :
  R.v56783 (state s) (inputs i) = Zmod.unsigned (N.v56783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56783 s i)) at 1.
  unfold R.v56783, N.v56783.
  rewrite ?node_56779.
  rewrite ?node_56782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56784 (s : N.State) (i : N.Inputs) :
  R.v56784 (state s) (inputs i) = Zmod.unsigned (N.v56784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56784 s i)) at 1.
  unfold R.v56784, N.v56784.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56785 (s : N.State) (i : N.Inputs) :
  R.v56785 (state s) (inputs i) = Zmod.unsigned (N.v56785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56785 s i)) at 1.
  unfold R.v56785, N.v56785.
  rewrite ?node_13851.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56786 (s : N.State) (i : N.Inputs) :
  R.v56786 (state s) (inputs i) = Zmod.unsigned (N.v56786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56786 s i)) at 1.
  unfold R.v56786, N.v56786.
  unfold R.v6, N.v6.
  rewrite ?node_13847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56787 (s : N.State) (i : N.Inputs) :
  R.v56787 (state s) (inputs i) = Zmod.unsigned (N.v56787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56787 s i)) at 1.
  unfold R.v56787, N.v56787.
  unfold R.v6, N.v6.
  rewrite ?node_13846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56788 (s : N.State) (i : N.Inputs) :
  R.v56788 (state s) (inputs i) = Zmod.unsigned (N.v56788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56788 s i)) at 1.
  unfold R.v56788, N.v56788.
  rewrite ?node_56786.
  rewrite ?node_56787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56789 (s : N.State) (i : N.Inputs) :
  R.v56789 (state s) (inputs i) = Zmod.unsigned (N.v56789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56789 s i)) at 1.
  unfold R.v56789, N.v56789.
  unfold R.v16484, N.v16484.
  rewrite ?node_56788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56790 (s : N.State) (i : N.Inputs) :
  R.v56790 (state s) (inputs i) = Zmod.unsigned (N.v56790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56790 s i)) at 1.
  unfold R.v56790, N.v56790.
  rewrite ?node_56785.
  rewrite ?node_56789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56791 (s : N.State) (i : N.Inputs) :
  R.v56791 (state s) (inputs i) = Zmod.unsigned (N.v56791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56791 s i)) at 1.
  unfold R.v56791, N.v56791.
  unfold R.v6, N.v6.
  rewrite ?node_56790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56792 (s : N.State) (i : N.Inputs) :
  R.v56792 (state s) (inputs i) = Zmod.unsigned (N.v56792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56792 s i)) at 1.
  unfold R.v56792, N.v56792.
  rewrite ?node_13852.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56793 (s : N.State) (i : N.Inputs) :
  R.v56793 (state s) (inputs i) = Zmod.unsigned (N.v56793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56793 s i)) at 1.
  unfold R.v56793, N.v56793.
  unfold R.v6, N.v6.
  rewrite ?node_13961.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56794 (s : N.State) (i : N.Inputs) :
  R.v56794 (state s) (inputs i) = Zmod.unsigned (N.v56794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56794 s i)) at 1.
  unfold R.v56794, N.v56794.
  rewrite ?node_56792.
  rewrite ?node_56793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56795 (s : N.State) (i : N.Inputs) :
  R.v56795 (state s) (inputs i) = Zmod.unsigned (N.v56795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56795 s i)) at 1.
  unfold R.v56795, N.v56795.
  rewrite ?node_56791.
  rewrite ?node_56794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56796 (s : N.State) (i : N.Inputs) :
  R.v56796 (state s) (inputs i) = Zmod.unsigned (N.v56796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56796 s i)) at 1.
  unfold R.v56796, N.v56796.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56797 (s : N.State) (i : N.Inputs) :
  R.v56797 (state s) (inputs i) = Zmod.unsigned (N.v56797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56797 s i)) at 1.
  unfold R.v56797, N.v56797.
  rewrite ?node_13957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56798 (s : N.State) (i : N.Inputs) :
  R.v56798 (state s) (inputs i) = Zmod.unsigned (N.v56798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56798 s i)) at 1.
  unfold R.v56798, N.v56798.
  rewrite ?node_13953.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56799 (s : N.State) (i : N.Inputs) :
  R.v56799 (state s) (inputs i) = Zmod.unsigned (N.v56799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56799 s i)) at 1.
  unfold R.v56799, N.v56799.
  rewrite ?node_13951.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56800 (s : N.State) (i : N.Inputs) :
  R.v56800 (state s) (inputs i) = Zmod.unsigned (N.v56800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56800 s i)) at 1.
  unfold R.v56800, N.v56800.
  unfold R.v6, N.v6.
  rewrite ?node_13947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56801 (s : N.State) (i : N.Inputs) :
  R.v56801 (state s) (inputs i) = Zmod.unsigned (N.v56801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56801 s i)) at 1.
  unfold R.v56801, N.v56801.
  unfold R.v6, N.v6.
  rewrite ?node_13940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56802 (s : N.State) (i : N.Inputs) :
  R.v56802 (state s) (inputs i) = Zmod.unsigned (N.v56802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56802 s i)) at 1.
  unfold R.v56802, N.v56802.
  rewrite ?node_56800.
  rewrite ?node_56801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56803 (s : N.State) (i : N.Inputs) :
  R.v56803 (state s) (inputs i) = Zmod.unsigned (N.v56803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56803 s i)) at 1.
  unfold R.v56803, N.v56803.
  unfold R.v16484, N.v16484.
  rewrite ?node_56802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56804 (s : N.State) (i : N.Inputs) :
  R.v56804 (state s) (inputs i) = Zmod.unsigned (N.v56804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56804 s i)) at 1.
  unfold R.v56804, N.v56804.
  rewrite ?node_56797.
  rewrite ?node_56798.
  rewrite ?node_56799.
  rewrite ?node_56803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56805 (s : N.State) (i : N.Inputs) :
  R.v56805 (state s) (inputs i) = Zmod.unsigned (N.v56805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56805 s i)) at 1.
  unfold R.v56805, N.v56805.
  unfold R.v6, N.v6.
  rewrite ?node_56804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56806 (s : N.State) (i : N.Inputs) :
  R.v56806 (state s) (inputs i) = Zmod.unsigned (N.v56806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56806 s i)) at 1.
  unfold R.v56806, N.v56806.
  rewrite ?node_13958.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56807 (s : N.State) (i : N.Inputs) :
  R.v56807 (state s) (inputs i) = Zmod.unsigned (N.v56807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56807 s i)) at 1.
  unfold R.v56807, N.v56807.
  unfold R.v6, N.v6.
  rewrite ?node_14062.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56808 (s : N.State) (i : N.Inputs) :
  R.v56808 (state s) (inputs i) = Zmod.unsigned (N.v56808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56808 s i)) at 1.
  unfold R.v56808, N.v56808.
  unfold R.v6, N.v6.
  rewrite ?node_14066.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56809 (s : N.State) (i : N.Inputs) :
  R.v56809 (state s) (inputs i) = Zmod.unsigned (N.v56809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56809 s i)) at 1.
  unfold R.v56809, N.v56809.
  rewrite ?node_56806.
  rewrite ?node_56807.
  rewrite ?node_56808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56810 (s : N.State) (i : N.Inputs) :
  R.v56810 (state s) (inputs i) = Zmod.unsigned (N.v56810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56810 s i)) at 1.
  unfold R.v56810, N.v56810.
  rewrite ?node_56805.
  rewrite ?node_56809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56811 (s : N.State) (i : N.Inputs) :
  R.v56811 (state s) (inputs i) = Zmod.unsigned (N.v56811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56811 s i)) at 1.
  unfold R.v56811, N.v56811.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56812 (s : N.State) (i : N.Inputs) :
  R.v56812 (state s) (inputs i) = Zmod.unsigned (N.v56812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56812 s i)) at 1.
  unfold R.v56812, N.v56812.
  rewrite ?node_13951.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56813 (s : N.State) (i : N.Inputs) :
  R.v56813 (state s) (inputs i) = Zmod.unsigned (N.v56813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56813 s i)) at 1.
  unfold R.v56813, N.v56813.
  unfold R.v6, N.v6.
  rewrite ?node_13947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56814 (s : N.State) (i : N.Inputs) :
  R.v56814 (state s) (inputs i) = Zmod.unsigned (N.v56814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56814 s i)) at 1.
  unfold R.v56814, N.v56814.
  unfold R.v6, N.v6.
  rewrite ?node_13940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56815 (s : N.State) (i : N.Inputs) :
  R.v56815 (state s) (inputs i) = Zmod.unsigned (N.v56815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56815 s i)) at 1.
  unfold R.v56815, N.v56815.
  rewrite ?node_56813.
  rewrite ?node_56814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56816 (s : N.State) (i : N.Inputs) :
  R.v56816 (state s) (inputs i) = Zmod.unsigned (N.v56816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56816 s i)) at 1.
  unfold R.v56816, N.v56816.
  unfold R.v16484, N.v16484.
  rewrite ?node_56815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56817 (s : N.State) (i : N.Inputs) :
  R.v56817 (state s) (inputs i) = Zmod.unsigned (N.v56817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56817 s i)) at 1.
  unfold R.v56817, N.v56817.
  rewrite ?node_56812.
  rewrite ?node_56816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56818 (s : N.State) (i : N.Inputs) :
  R.v56818 (state s) (inputs i) = Zmod.unsigned (N.v56818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56818 s i)) at 1.
  unfold R.v56818, N.v56818.
  unfold R.v6, N.v6.
  rewrite ?node_56817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56819 (s : N.State) (i : N.Inputs) :
  R.v56819 (state s) (inputs i) = Zmod.unsigned (N.v56819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56819 s i)) at 1.
  unfold R.v56819, N.v56819.
  rewrite ?node_13952.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56820 (s : N.State) (i : N.Inputs) :
  R.v56820 (state s) (inputs i) = Zmod.unsigned (N.v56820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56820 s i)) at 1.
  unfold R.v56820, N.v56820.
  unfold R.v6, N.v6.
  rewrite ?node_14062.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56821 (s : N.State) (i : N.Inputs) :
  R.v56821 (state s) (inputs i) = Zmod.unsigned (N.v56821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56821 s i)) at 1.
  unfold R.v56821, N.v56821.
  rewrite ?node_56819.
  rewrite ?node_56820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56822 (s : N.State) (i : N.Inputs) :
  R.v56822 (state s) (inputs i) = Zmod.unsigned (N.v56822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56822 s i)) at 1.
  unfold R.v56822, N.v56822.
  rewrite ?node_56818.
  rewrite ?node_56821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56823 (s : N.State) (i : N.Inputs) :
  R.v56823 (state s) (inputs i) = Zmod.unsigned (N.v56823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56823 s i)) at 1.
  unfold R.v56823, N.v56823.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56824 (s : N.State) (i : N.Inputs) :
  R.v56824 (state s) (inputs i) = Zmod.unsigned (N.v56824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56824 s i)) at 1.
  unfold R.v56824, N.v56824.
  rewrite ?node_13957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56825 (s : N.State) (i : N.Inputs) :
  R.v56825 (state s) (inputs i) = Zmod.unsigned (N.v56825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56825 s i)) at 1.
  unfold R.v56825, N.v56825.
  unfold R.v6, N.v6.
  rewrite ?node_13953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56826 (s : N.State) (i : N.Inputs) :
  R.v56826 (state s) (inputs i) = Zmod.unsigned (N.v56826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56826 s i)) at 1.
  unfold R.v56826, N.v56826.
  unfold R.v6, N.v6.
  rewrite ?node_13952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56827 (s : N.State) (i : N.Inputs) :
  R.v56827 (state s) (inputs i) = Zmod.unsigned (N.v56827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56827 s i)) at 1.
  unfold R.v56827, N.v56827.
  rewrite ?node_56825.
  rewrite ?node_56826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56828 (s : N.State) (i : N.Inputs) :
  R.v56828 (state s) (inputs i) = Zmod.unsigned (N.v56828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56828 s i)) at 1.
  unfold R.v56828, N.v56828.
  unfold R.v16484, N.v16484.
  rewrite ?node_56827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56829 (s : N.State) (i : N.Inputs) :
  R.v56829 (state s) (inputs i) = Zmod.unsigned (N.v56829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56829 s i)) at 1.
  unfold R.v56829, N.v56829.
  rewrite ?node_56824.
  rewrite ?node_56828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56830 (s : N.State) (i : N.Inputs) :
  R.v56830 (state s) (inputs i) = Zmod.unsigned (N.v56830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56830 s i)) at 1.
  unfold R.v56830, N.v56830.
  unfold R.v6, N.v6.
  rewrite ?node_56829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56831 (s : N.State) (i : N.Inputs) :
  R.v56831 (state s) (inputs i) = Zmod.unsigned (N.v56831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56831 s i)) at 1.
  unfold R.v56831, N.v56831.
  rewrite ?node_13958.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56832 (s : N.State) (i : N.Inputs) :
  R.v56832 (state s) (inputs i) = Zmod.unsigned (N.v56832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56832 s i)) at 1.
  unfold R.v56832, N.v56832.
  unfold R.v6, N.v6.
  rewrite ?node_14066.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56833 (s : N.State) (i : N.Inputs) :
  R.v56833 (state s) (inputs i) = Zmod.unsigned (N.v56833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56833 s i)) at 1.
  unfold R.v56833, N.v56833.
  rewrite ?node_56831.
  rewrite ?node_56832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56834 (s : N.State) (i : N.Inputs) :
  R.v56834 (state s) (inputs i) = Zmod.unsigned (N.v56834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56834 s i)) at 1.
  unfold R.v56834, N.v56834.
  rewrite ?node_56830.
  rewrite ?node_56833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56835 (s : N.State) (i : N.Inputs) :
  R.v56835 (state s) (inputs i) = Zmod.unsigned (N.v56835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56835 s i)) at 1.
  unfold R.v56835, N.v56835.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56836 (s : N.State) (i : N.Inputs) :
  R.v56836 (state s) (inputs i) = Zmod.unsigned (N.v56836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56836 s i)) at 1.
  unfold R.v56836, N.v56836.
  rewrite ?node_14062.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56837 (s : N.State) (i : N.Inputs) :
  R.v56837 (state s) (inputs i) = Zmod.unsigned (N.v56837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56837 s i)) at 1.
  unfold R.v56837, N.v56837.
  rewrite ?node_14058.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56838 (s : N.State) (i : N.Inputs) :
  R.v56838 (state s) (inputs i) = Zmod.unsigned (N.v56838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56838 s i)) at 1.
  unfold R.v56838, N.v56838.
  rewrite ?node_14056.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56839 (s : N.State) (i : N.Inputs) :
  R.v56839 (state s) (inputs i) = Zmod.unsigned (N.v56839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56839 s i)) at 1.
  unfold R.v56839, N.v56839.
  unfold R.v6, N.v6.
  rewrite ?node_14052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56840 (s : N.State) (i : N.Inputs) :
  R.v56840 (state s) (inputs i) = Zmod.unsigned (N.v56840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56840 s i)) at 1.
  unfold R.v56840, N.v56840.
  unfold R.v6, N.v6.
  rewrite ?node_14041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56841 (s : N.State) (i : N.Inputs) :
  R.v56841 (state s) (inputs i) = Zmod.unsigned (N.v56841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56841 s i)) at 1.
  unfold R.v56841, N.v56841.
  rewrite ?node_56839.
  rewrite ?node_56840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56842 (s : N.State) (i : N.Inputs) :
  R.v56842 (state s) (inputs i) = Zmod.unsigned (N.v56842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56842 s i)) at 1.
  unfold R.v56842, N.v56842.
  unfold R.v16484, N.v16484.
  rewrite ?node_56841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56843 (s : N.State) (i : N.Inputs) :
  R.v56843 (state s) (inputs i) = Zmod.unsigned (N.v56843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56843 s i)) at 1.
  unfold R.v56843, N.v56843.
  rewrite ?node_56836.
  rewrite ?node_56837.
  rewrite ?node_56838.
  rewrite ?node_56842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56844 (s : N.State) (i : N.Inputs) :
  R.v56844 (state s) (inputs i) = Zmod.unsigned (N.v56844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56844 s i)) at 1.
  unfold R.v56844, N.v56844.
  unfold R.v6, N.v6.
  rewrite ?node_56843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56845 (s : N.State) (i : N.Inputs) :
  R.v56845 (state s) (inputs i) = Zmod.unsigned (N.v56845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56845 s i)) at 1.
  unfold R.v56845, N.v56845.
  rewrite ?node_14063.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56846 (s : N.State) (i : N.Inputs) :
  R.v56846 (state s) (inputs i) = Zmod.unsigned (N.v56846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56846 s i)) at 1.
  unfold R.v56846, N.v56846.
  unfold R.v6, N.v6.
  rewrite ?node_14163.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56847 (s : N.State) (i : N.Inputs) :
  R.v56847 (state s) (inputs i) = Zmod.unsigned (N.v56847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56847 s i)) at 1.
  unfold R.v56847, N.v56847.
  unfold R.v6, N.v6.
  rewrite ?node_14167.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56848 (s : N.State) (i : N.Inputs) :
  R.v56848 (state s) (inputs i) = Zmod.unsigned (N.v56848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56848 s i)) at 1.
  unfold R.v56848, N.v56848.
  rewrite ?node_56845.
  rewrite ?node_56846.
  rewrite ?node_56847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56849 (s : N.State) (i : N.Inputs) :
  R.v56849 (state s) (inputs i) = Zmod.unsigned (N.v56849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56849 s i)) at 1.
  unfold R.v56849, N.v56849.
  rewrite ?node_56844.
  rewrite ?node_56848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56850 (s : N.State) (i : N.Inputs) :
  R.v56850 (state s) (inputs i) = Zmod.unsigned (N.v56850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56850 s i)) at 1.
  unfold R.v56850, N.v56850.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56851 (s : N.State) (i : N.Inputs) :
  R.v56851 (state s) (inputs i) = Zmod.unsigned (N.v56851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56851 s i)) at 1.
  unfold R.v56851, N.v56851.
  rewrite ?node_14056.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56852 (s : N.State) (i : N.Inputs) :
  R.v56852 (state s) (inputs i) = Zmod.unsigned (N.v56852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56852 s i)) at 1.
  unfold R.v56852, N.v56852.
  unfold R.v6, N.v6.
  rewrite ?node_14052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56853 (s : N.State) (i : N.Inputs) :
  R.v56853 (state s) (inputs i) = Zmod.unsigned (N.v56853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56853 s i)) at 1.
  unfold R.v56853, N.v56853.
  unfold R.v6, N.v6.
  rewrite ?node_14041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56854 (s : N.State) (i : N.Inputs) :
  R.v56854 (state s) (inputs i) = Zmod.unsigned (N.v56854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56854 s i)) at 1.
  unfold R.v56854, N.v56854.
  rewrite ?node_56852.
  rewrite ?node_56853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56855 (s : N.State) (i : N.Inputs) :
  R.v56855 (state s) (inputs i) = Zmod.unsigned (N.v56855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56855 s i)) at 1.
  unfold R.v56855, N.v56855.
  unfold R.v16484, N.v16484.
  rewrite ?node_56854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56856 (s : N.State) (i : N.Inputs) :
  R.v56856 (state s) (inputs i) = Zmod.unsigned (N.v56856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56856 s i)) at 1.
  unfold R.v56856, N.v56856.
  rewrite ?node_56851.
  rewrite ?node_56855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56857 (s : N.State) (i : N.Inputs) :
  R.v56857 (state s) (inputs i) = Zmod.unsigned (N.v56857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56857 s i)) at 1.
  unfold R.v56857, N.v56857.
  unfold R.v6, N.v6.
  rewrite ?node_56856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56858 (s : N.State) (i : N.Inputs) :
  R.v56858 (state s) (inputs i) = Zmod.unsigned (N.v56858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56858 s i)) at 1.
  unfold R.v56858, N.v56858.
  rewrite ?node_14057.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56859 (s : N.State) (i : N.Inputs) :
  R.v56859 (state s) (inputs i) = Zmod.unsigned (N.v56859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56859 s i)) at 1.
  unfold R.v56859, N.v56859.
  unfold R.v6, N.v6.
  rewrite ?node_14163.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56860 (s : N.State) (i : N.Inputs) :
  R.v56860 (state s) (inputs i) = Zmod.unsigned (N.v56860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56860 s i)) at 1.
  unfold R.v56860, N.v56860.
  rewrite ?node_56858.
  rewrite ?node_56859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56861 (s : N.State) (i : N.Inputs) :
  R.v56861 (state s) (inputs i) = Zmod.unsigned (N.v56861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56861 s i)) at 1.
  unfold R.v56861, N.v56861.
  rewrite ?node_56857.
  rewrite ?node_56860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56862 (s : N.State) (i : N.Inputs) :
  R.v56862 (state s) (inputs i) = Zmod.unsigned (N.v56862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56862 s i)) at 1.
  unfold R.v56862, N.v56862.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56863 (s : N.State) (i : N.Inputs) :
  R.v56863 (state s) (inputs i) = Zmod.unsigned (N.v56863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56863 s i)) at 1.
  unfold R.v56863, N.v56863.
  rewrite ?node_14062.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56864 (s : N.State) (i : N.Inputs) :
  R.v56864 (state s) (inputs i) = Zmod.unsigned (N.v56864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56864 s i)) at 1.
  unfold R.v56864, N.v56864.
  unfold R.v6, N.v6.
  rewrite ?node_14058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56865 (s : N.State) (i : N.Inputs) :
  R.v56865 (state s) (inputs i) = Zmod.unsigned (N.v56865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56865 s i)) at 1.
  unfold R.v56865, N.v56865.
  unfold R.v6, N.v6.
  rewrite ?node_14057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56866 (s : N.State) (i : N.Inputs) :
  R.v56866 (state s) (inputs i) = Zmod.unsigned (N.v56866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56866 s i)) at 1.
  unfold R.v56866, N.v56866.
  rewrite ?node_56864.
  rewrite ?node_56865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56867 (s : N.State) (i : N.Inputs) :
  R.v56867 (state s) (inputs i) = Zmod.unsigned (N.v56867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56867 s i)) at 1.
  unfold R.v56867, N.v56867.
  unfold R.v16484, N.v16484.
  rewrite ?node_56866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56868 (s : N.State) (i : N.Inputs) :
  R.v56868 (state s) (inputs i) = Zmod.unsigned (N.v56868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56868 s i)) at 1.
  unfold R.v56868, N.v56868.
  rewrite ?node_56863.
  rewrite ?node_56867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56869 (s : N.State) (i : N.Inputs) :
  R.v56869 (state s) (inputs i) = Zmod.unsigned (N.v56869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56869 s i)) at 1.
  unfold R.v56869, N.v56869.
  unfold R.v6, N.v6.
  rewrite ?node_56868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56870 (s : N.State) (i : N.Inputs) :
  R.v56870 (state s) (inputs i) = Zmod.unsigned (N.v56870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56870 s i)) at 1.
  unfold R.v56870, N.v56870.
  rewrite ?node_14063.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56871 (s : N.State) (i : N.Inputs) :
  R.v56871 (state s) (inputs i) = Zmod.unsigned (N.v56871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56871 s i)) at 1.
  unfold R.v56871, N.v56871.
  unfold R.v6, N.v6.
  rewrite ?node_14167.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56872 (s : N.State) (i : N.Inputs) :
  R.v56872 (state s) (inputs i) = Zmod.unsigned (N.v56872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56872 s i)) at 1.
  unfold R.v56872, N.v56872.
  rewrite ?node_56870.
  rewrite ?node_56871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56873 (s : N.State) (i : N.Inputs) :
  R.v56873 (state s) (inputs i) = Zmod.unsigned (N.v56873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56873 s i)) at 1.
  unfold R.v56873, N.v56873.
  rewrite ?node_56869.
  rewrite ?node_56872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56874 (s : N.State) (i : N.Inputs) :
  R.v56874 (state s) (inputs i) = Zmod.unsigned (N.v56874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56874 s i)) at 1.
  unfold R.v56874, N.v56874.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56875 (s : N.State) (i : N.Inputs) :
  R.v56875 (state s) (inputs i) = Zmod.unsigned (N.v56875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56875 s i)) at 1.
  unfold R.v56875, N.v56875.
  rewrite ?node_14163.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56876 (s : N.State) (i : N.Inputs) :
  R.v56876 (state s) (inputs i) = Zmod.unsigned (N.v56876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56876 s i)) at 1.
  unfold R.v56876, N.v56876.
  rewrite ?node_14159.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56877 (s : N.State) (i : N.Inputs) :
  R.v56877 (state s) (inputs i) = Zmod.unsigned (N.v56877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56877 s i)) at 1.
  unfold R.v56877, N.v56877.
  rewrite ?node_14155.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56878 (s : N.State) (i : N.Inputs) :
  R.v56878 (state s) (inputs i) = Zmod.unsigned (N.v56878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56878 s i)) at 1.
  unfold R.v56878, N.v56878.
  unfold R.v6, N.v6.
  rewrite ?node_14151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56879 (s : N.State) (i : N.Inputs) :
  R.v56879 (state s) (inputs i) = Zmod.unsigned (N.v56879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56879 s i)) at 1.
  unfold R.v56879, N.v56879.
  unfold R.v6, N.v6.
  rewrite ?node_14144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56880 (s : N.State) (i : N.Inputs) :
  R.v56880 (state s) (inputs i) = Zmod.unsigned (N.v56880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56880 s i)) at 1.
  unfold R.v56880, N.v56880.
  rewrite ?node_56878.
  rewrite ?node_56879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56881 (s : N.State) (i : N.Inputs) :
  R.v56881 (state s) (inputs i) = Zmod.unsigned (N.v56881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56881 s i)) at 1.
  unfold R.v56881, N.v56881.
  unfold R.v16484, N.v16484.
  rewrite ?node_56880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56882 (s : N.State) (i : N.Inputs) :
  R.v56882 (state s) (inputs i) = Zmod.unsigned (N.v56882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56882 s i)) at 1.
  unfold R.v56882, N.v56882.
  rewrite ?node_56875.
  rewrite ?node_56876.
  rewrite ?node_56877.
  rewrite ?node_56881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56883 (s : N.State) (i : N.Inputs) :
  R.v56883 (state s) (inputs i) = Zmod.unsigned (N.v56883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56883 s i)) at 1.
  unfold R.v56883, N.v56883.
  unfold R.v6, N.v6.
  rewrite ?node_56882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56884 (s : N.State) (i : N.Inputs) :
  R.v56884 (state s) (inputs i) = Zmod.unsigned (N.v56884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56884 s i)) at 1.
  unfold R.v56884, N.v56884.
  rewrite ?node_14164.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56885 (s : N.State) (i : N.Inputs) :
  R.v56885 (state s) (inputs i) = Zmod.unsigned (N.v56885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56885 s i)) at 1.
  unfold R.v56885, N.v56885.
  unfold R.v6, N.v6.
  rewrite ?node_14261.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56886 (s : N.State) (i : N.Inputs) :
  R.v56886 (state s) (inputs i) = Zmod.unsigned (N.v56886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56886 s i)) at 1.
  unfold R.v56886, N.v56886.
  unfold R.v6, N.v6.
  rewrite ?node_14265.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56887 (s : N.State) (i : N.Inputs) :
  R.v56887 (state s) (inputs i) = Zmod.unsigned (N.v56887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56887 s i)) at 1.
  unfold R.v56887, N.v56887.
  rewrite ?node_56884.
  rewrite ?node_56885.
  rewrite ?node_56886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56888 (s : N.State) (i : N.Inputs) :
  R.v56888 (state s) (inputs i) = Zmod.unsigned (N.v56888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56888 s i)) at 1.
  unfold R.v56888, N.v56888.
  rewrite ?node_56883.
  rewrite ?node_56887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56889 (s : N.State) (i : N.Inputs) :
  R.v56889 (state s) (inputs i) = Zmod.unsigned (N.v56889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56889 s i)) at 1.
  unfold R.v56889, N.v56889.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56890 (s : N.State) (i : N.Inputs) :
  R.v56890 (state s) (inputs i) = Zmod.unsigned (N.v56890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56890 s i)) at 1.
  unfold R.v56890, N.v56890.
  rewrite ?node_14155.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56891 (s : N.State) (i : N.Inputs) :
  R.v56891 (state s) (inputs i) = Zmod.unsigned (N.v56891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56891 s i)) at 1.
  unfold R.v56891, N.v56891.
  unfold R.v6, N.v6.
  rewrite ?node_14151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56892 (s : N.State) (i : N.Inputs) :
  R.v56892 (state s) (inputs i) = Zmod.unsigned (N.v56892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56892 s i)) at 1.
  unfold R.v56892, N.v56892.
  unfold R.v6, N.v6.
  rewrite ?node_14144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56893 (s : N.State) (i : N.Inputs) :
  R.v56893 (state s) (inputs i) = Zmod.unsigned (N.v56893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56893 s i)) at 1.
  unfold R.v56893, N.v56893.
  rewrite ?node_56891.
  rewrite ?node_56892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56894 (s : N.State) (i : N.Inputs) :
  R.v56894 (state s) (inputs i) = Zmod.unsigned (N.v56894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56894 s i)) at 1.
  unfold R.v56894, N.v56894.
  unfold R.v16484, N.v16484.
  rewrite ?node_56893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56895 (s : N.State) (i : N.Inputs) :
  R.v56895 (state s) (inputs i) = Zmod.unsigned (N.v56895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56895 s i)) at 1.
  unfold R.v56895, N.v56895.
  rewrite ?node_56890.
  rewrite ?node_56894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56896 (s : N.State) (i : N.Inputs) :
  R.v56896 (state s) (inputs i) = Zmod.unsigned (N.v56896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56896 s i)) at 1.
  unfold R.v56896, N.v56896.
  unfold R.v6, N.v6.
  rewrite ?node_56895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56897 (s : N.State) (i : N.Inputs) :
  R.v56897 (state s) (inputs i) = Zmod.unsigned (N.v56897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56897 s i)) at 1.
  unfold R.v56897, N.v56897.
  rewrite ?node_14156.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56898 (s : N.State) (i : N.Inputs) :
  R.v56898 (state s) (inputs i) = Zmod.unsigned (N.v56898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56898 s i)) at 1.
  unfold R.v56898, N.v56898.
  unfold R.v6, N.v6.
  rewrite ?node_14261.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56899 (s : N.State) (i : N.Inputs) :
  R.v56899 (state s) (inputs i) = Zmod.unsigned (N.v56899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56899 s i)) at 1.
  unfold R.v56899, N.v56899.
  rewrite ?node_56897.
  rewrite ?node_56898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56900 (s : N.State) (i : N.Inputs) :
  R.v56900 (state s) (inputs i) = Zmod.unsigned (N.v56900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56900 s i)) at 1.
  unfold R.v56900, N.v56900.
  rewrite ?node_56896.
  rewrite ?node_56899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56901 (s : N.State) (i : N.Inputs) :
  R.v56901 (state s) (inputs i) = Zmod.unsigned (N.v56901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56901 s i)) at 1.
  unfold R.v56901, N.v56901.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56902 (s : N.State) (i : N.Inputs) :
  R.v56902 (state s) (inputs i) = Zmod.unsigned (N.v56902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56902 s i)) at 1.
  unfold R.v56902, N.v56902.
  rewrite ?node_14163.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56903 (s : N.State) (i : N.Inputs) :
  R.v56903 (state s) (inputs i) = Zmod.unsigned (N.v56903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56903 s i)) at 1.
  unfold R.v56903, N.v56903.
  unfold R.v6, N.v6.
  rewrite ?node_14159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56904 (s : N.State) (i : N.Inputs) :
  R.v56904 (state s) (inputs i) = Zmod.unsigned (N.v56904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56904 s i)) at 1.
  unfold R.v56904, N.v56904.
  unfold R.v6, N.v6.
  rewrite ?node_14156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56905 (s : N.State) (i : N.Inputs) :
  R.v56905 (state s) (inputs i) = Zmod.unsigned (N.v56905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56905 s i)) at 1.
  unfold R.v56905, N.v56905.
  rewrite ?node_56903.
  rewrite ?node_56904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56906 (s : N.State) (i : N.Inputs) :
  R.v56906 (state s) (inputs i) = Zmod.unsigned (N.v56906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56906 s i)) at 1.
  unfold R.v56906, N.v56906.
  unfold R.v16484, N.v16484.
  rewrite ?node_56905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56907 (s : N.State) (i : N.Inputs) :
  R.v56907 (state s) (inputs i) = Zmod.unsigned (N.v56907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56907 s i)) at 1.
  unfold R.v56907, N.v56907.
  rewrite ?node_56902.
  rewrite ?node_56906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56908 (s : N.State) (i : N.Inputs) :
  R.v56908 (state s) (inputs i) = Zmod.unsigned (N.v56908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56908 s i)) at 1.
  unfold R.v56908, N.v56908.
  unfold R.v6, N.v6.
  rewrite ?node_56907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56909 (s : N.State) (i : N.Inputs) :
  R.v56909 (state s) (inputs i) = Zmod.unsigned (N.v56909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56909 s i)) at 1.
  unfold R.v56909, N.v56909.
  rewrite ?node_14164.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56910 (s : N.State) (i : N.Inputs) :
  R.v56910 (state s) (inputs i) = Zmod.unsigned (N.v56910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56910 s i)) at 1.
  unfold R.v56910, N.v56910.
  unfold R.v6, N.v6.
  rewrite ?node_14265.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56911 (s : N.State) (i : N.Inputs) :
  R.v56911 (state s) (inputs i) = Zmod.unsigned (N.v56911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56911 s i)) at 1.
  unfold R.v56911, N.v56911.
  rewrite ?node_56909.
  rewrite ?node_56910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56912 (s : N.State) (i : N.Inputs) :
  R.v56912 (state s) (inputs i) = Zmod.unsigned (N.v56912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56912 s i)) at 1.
  unfold R.v56912, N.v56912.
  rewrite ?node_56908.
  rewrite ?node_56911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56913 (s : N.State) (i : N.Inputs) :
  R.v56913 (state s) (inputs i) = Zmod.unsigned (N.v56913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56913 s i)) at 1.
  unfold R.v56913, N.v56913.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56914 (s : N.State) (i : N.Inputs) :
  R.v56914 (state s) (inputs i) = Zmod.unsigned (N.v56914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56914 s i)) at 1.
  unfold R.v56914, N.v56914.
  rewrite ?node_14261.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56915 (s : N.State) (i : N.Inputs) :
  R.v56915 (state s) (inputs i) = Zmod.unsigned (N.v56915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56915 s i)) at 1.
  unfold R.v56915, N.v56915.
  rewrite ?node_14257.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56916 (s : N.State) (i : N.Inputs) :
  R.v56916 (state s) (inputs i) = Zmod.unsigned (N.v56916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56916 s i)) at 1.
  unfold R.v56916, N.v56916.
  rewrite ?node_14255.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56917 (s : N.State) (i : N.Inputs) :
  R.v56917 (state s) (inputs i) = Zmod.unsigned (N.v56917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56917 s i)) at 1.
  unfold R.v56917, N.v56917.
  unfold R.v6, N.v6.
  rewrite ?node_14251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56918 (s : N.State) (i : N.Inputs) :
  R.v56918 (state s) (inputs i) = Zmod.unsigned (N.v56918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56918 s i)) at 1.
  unfold R.v56918, N.v56918.
  unfold R.v6, N.v6.
  rewrite ?node_14246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56919 (s : N.State) (i : N.Inputs) :
  R.v56919 (state s) (inputs i) = Zmod.unsigned (N.v56919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56919 s i)) at 1.
  unfold R.v56919, N.v56919.
  rewrite ?node_56917.
  rewrite ?node_56918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56920 (s : N.State) (i : N.Inputs) :
  R.v56920 (state s) (inputs i) = Zmod.unsigned (N.v56920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56920 s i)) at 1.
  unfold R.v56920, N.v56920.
  unfold R.v16484, N.v16484.
  rewrite ?node_56919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56921 (s : N.State) (i : N.Inputs) :
  R.v56921 (state s) (inputs i) = Zmod.unsigned (N.v56921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56921 s i)) at 1.
  unfold R.v56921, N.v56921.
  rewrite ?node_56914.
  rewrite ?node_56915.
  rewrite ?node_56916.
  rewrite ?node_56920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56922 (s : N.State) (i : N.Inputs) :
  R.v56922 (state s) (inputs i) = Zmod.unsigned (N.v56922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56922 s i)) at 1.
  unfold R.v56922, N.v56922.
  unfold R.v6, N.v6.
  rewrite ?node_56921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56923 (s : N.State) (i : N.Inputs) :
  R.v56923 (state s) (inputs i) = Zmod.unsigned (N.v56923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56923 s i)) at 1.
  unfold R.v56923, N.v56923.
  rewrite ?node_14262.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56924 (s : N.State) (i : N.Inputs) :
  R.v56924 (state s) (inputs i) = Zmod.unsigned (N.v56924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56924 s i)) at 1.
  unfold R.v56924, N.v56924.
  unfold R.v6, N.v6.
  rewrite ?node_14357.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56925 (s : N.State) (i : N.Inputs) :
  R.v56925 (state s) (inputs i) = Zmod.unsigned (N.v56925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56925 s i)) at 1.
  unfold R.v56925, N.v56925.
  unfold R.v6, N.v6.
  rewrite ?node_14361.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56926 (s : N.State) (i : N.Inputs) :
  R.v56926 (state s) (inputs i) = Zmod.unsigned (N.v56926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56926 s i)) at 1.
  unfold R.v56926, N.v56926.
  rewrite ?node_56923.
  rewrite ?node_56924.
  rewrite ?node_56925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56927 (s : N.State) (i : N.Inputs) :
  R.v56927 (state s) (inputs i) = Zmod.unsigned (N.v56927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56927 s i)) at 1.
  unfold R.v56927, N.v56927.
  rewrite ?node_56922.
  rewrite ?node_56926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56928 (s : N.State) (i : N.Inputs) :
  R.v56928 (state s) (inputs i) = Zmod.unsigned (N.v56928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56928 s i)) at 1.
  unfold R.v56928, N.v56928.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56929 (s : N.State) (i : N.Inputs) :
  R.v56929 (state s) (inputs i) = Zmod.unsigned (N.v56929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56929 s i)) at 1.
  unfold R.v56929, N.v56929.
  rewrite ?node_14255.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56930 (s : N.State) (i : N.Inputs) :
  R.v56930 (state s) (inputs i) = Zmod.unsigned (N.v56930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56930 s i)) at 1.
  unfold R.v56930, N.v56930.
  unfold R.v6, N.v6.
  rewrite ?node_14251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56931 (s : N.State) (i : N.Inputs) :
  R.v56931 (state s) (inputs i) = Zmod.unsigned (N.v56931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56931 s i)) at 1.
  unfold R.v56931, N.v56931.
  unfold R.v6, N.v6.
  rewrite ?node_14246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56932 (s : N.State) (i : N.Inputs) :
  R.v56932 (state s) (inputs i) = Zmod.unsigned (N.v56932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56932 s i)) at 1.
  unfold R.v56932, N.v56932.
  rewrite ?node_56930.
  rewrite ?node_56931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56933 (s : N.State) (i : N.Inputs) :
  R.v56933 (state s) (inputs i) = Zmod.unsigned (N.v56933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56933 s i)) at 1.
  unfold R.v56933, N.v56933.
  unfold R.v16484, N.v16484.
  rewrite ?node_56932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56934 (s : N.State) (i : N.Inputs) :
  R.v56934 (state s) (inputs i) = Zmod.unsigned (N.v56934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56934 s i)) at 1.
  unfold R.v56934, N.v56934.
  rewrite ?node_56929.
  rewrite ?node_56933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56935 (s : N.State) (i : N.Inputs) :
  R.v56935 (state s) (inputs i) = Zmod.unsigned (N.v56935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56935 s i)) at 1.
  unfold R.v56935, N.v56935.
  unfold R.v6, N.v6.
  rewrite ?node_56934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56936 (s : N.State) (i : N.Inputs) :
  R.v56936 (state s) (inputs i) = Zmod.unsigned (N.v56936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56936 s i)) at 1.
  unfold R.v56936, N.v56936.
  rewrite ?node_14256.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56937 (s : N.State) (i : N.Inputs) :
  R.v56937 (state s) (inputs i) = Zmod.unsigned (N.v56937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56937 s i)) at 1.
  unfold R.v56937, N.v56937.
  unfold R.v6, N.v6.
  rewrite ?node_14357.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56938 (s : N.State) (i : N.Inputs) :
  R.v56938 (state s) (inputs i) = Zmod.unsigned (N.v56938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56938 s i)) at 1.
  unfold R.v56938, N.v56938.
  rewrite ?node_56936.
  rewrite ?node_56937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56939 (s : N.State) (i : N.Inputs) :
  R.v56939 (state s) (inputs i) = Zmod.unsigned (N.v56939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56939 s i)) at 1.
  unfold R.v56939, N.v56939.
  rewrite ?node_56935.
  rewrite ?node_56938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56940 (s : N.State) (i : N.Inputs) :
  R.v56940 (state s) (inputs i) = Zmod.unsigned (N.v56940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56940 s i)) at 1.
  unfold R.v56940, N.v56940.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56941 (s : N.State) (i : N.Inputs) :
  R.v56941 (state s) (inputs i) = Zmod.unsigned (N.v56941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56941 s i)) at 1.
  unfold R.v56941, N.v56941.
  rewrite ?node_14261.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56942 (s : N.State) (i : N.Inputs) :
  R.v56942 (state s) (inputs i) = Zmod.unsigned (N.v56942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56942 s i)) at 1.
  unfold R.v56942, N.v56942.
  unfold R.v6, N.v6.
  rewrite ?node_14257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56943 (s : N.State) (i : N.Inputs) :
  R.v56943 (state s) (inputs i) = Zmod.unsigned (N.v56943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56943 s i)) at 1.
  unfold R.v56943, N.v56943.
  unfold R.v6, N.v6.
  rewrite ?node_14256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56944 (s : N.State) (i : N.Inputs) :
  R.v56944 (state s) (inputs i) = Zmod.unsigned (N.v56944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56944 s i)) at 1.
  unfold R.v56944, N.v56944.
  rewrite ?node_56942.
  rewrite ?node_56943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56945 (s : N.State) (i : N.Inputs) :
  R.v56945 (state s) (inputs i) = Zmod.unsigned (N.v56945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56945 s i)) at 1.
  unfold R.v56945, N.v56945.
  unfold R.v16484, N.v16484.
  rewrite ?node_56944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56946 (s : N.State) (i : N.Inputs) :
  R.v56946 (state s) (inputs i) = Zmod.unsigned (N.v56946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56946 s i)) at 1.
  unfold R.v56946, N.v56946.
  rewrite ?node_56941.
  rewrite ?node_56945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56947 (s : N.State) (i : N.Inputs) :
  R.v56947 (state s) (inputs i) = Zmod.unsigned (N.v56947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56947 s i)) at 1.
  unfold R.v56947, N.v56947.
  unfold R.v6, N.v6.
  rewrite ?node_56946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56948 (s : N.State) (i : N.Inputs) :
  R.v56948 (state s) (inputs i) = Zmod.unsigned (N.v56948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56948 s i)) at 1.
  unfold R.v56948, N.v56948.
  rewrite ?node_14262.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56949 (s : N.State) (i : N.Inputs) :
  R.v56949 (state s) (inputs i) = Zmod.unsigned (N.v56949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56949 s i)) at 1.
  unfold R.v56949, N.v56949.
  unfold R.v6, N.v6.
  rewrite ?node_14361.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56950 (s : N.State) (i : N.Inputs) :
  R.v56950 (state s) (inputs i) = Zmod.unsigned (N.v56950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56950 s i)) at 1.
  unfold R.v56950, N.v56950.
  rewrite ?node_56948.
  rewrite ?node_56949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56951 (s : N.State) (i : N.Inputs) :
  R.v56951 (state s) (inputs i) = Zmod.unsigned (N.v56951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56951 s i)) at 1.
  unfold R.v56951, N.v56951.
  rewrite ?node_56947.
  rewrite ?node_56950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56952 (s : N.State) (i : N.Inputs) :
  R.v56952 (state s) (inputs i) = Zmod.unsigned (N.v56952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56952 s i)) at 1.
  unfold R.v56952, N.v56952.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56953 (s : N.State) (i : N.Inputs) :
  R.v56953 (state s) (inputs i) = Zmod.unsigned (N.v56953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56953 s i)) at 1.
  unfold R.v56953, N.v56953.
  rewrite ?node_14357.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56954 (s : N.State) (i : N.Inputs) :
  R.v56954 (state s) (inputs i) = Zmod.unsigned (N.v56954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56954 s i)) at 1.
  unfold R.v56954, N.v56954.
  rewrite ?node_14353.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56955 (s : N.State) (i : N.Inputs) :
  R.v56955 (state s) (inputs i) = Zmod.unsigned (N.v56955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56955 s i)) at 1.
  unfold R.v56955, N.v56955.
  rewrite ?node_14351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56956 (s : N.State) (i : N.Inputs) :
  R.v56956 (state s) (inputs i) = Zmod.unsigned (N.v56956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56956 s i)) at 1.
  unfold R.v56956, N.v56956.
  unfold R.v6, N.v6.
  rewrite ?node_14347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56957 (s : N.State) (i : N.Inputs) :
  R.v56957 (state s) (inputs i) = Zmod.unsigned (N.v56957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56957 s i)) at 1.
  unfold R.v56957, N.v56957.
  unfold R.v6, N.v6.
  rewrite ?node_14342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56958 (s : N.State) (i : N.Inputs) :
  R.v56958 (state s) (inputs i) = Zmod.unsigned (N.v56958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56958 s i)) at 1.
  unfold R.v56958, N.v56958.
  rewrite ?node_56956.
  rewrite ?node_56957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56959 (s : N.State) (i : N.Inputs) :
  R.v56959 (state s) (inputs i) = Zmod.unsigned (N.v56959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56959 s i)) at 1.
  unfold R.v56959, N.v56959.
  unfold R.v16484, N.v16484.
  rewrite ?node_56958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56960 (s : N.State) (i : N.Inputs) :
  R.v56960 (state s) (inputs i) = Zmod.unsigned (N.v56960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56960 s i)) at 1.
  unfold R.v56960, N.v56960.
  rewrite ?node_56953.
  rewrite ?node_56954.
  rewrite ?node_56955.
  rewrite ?node_56959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56961 (s : N.State) (i : N.Inputs) :
  R.v56961 (state s) (inputs i) = Zmod.unsigned (N.v56961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56961 s i)) at 1.
  unfold R.v56961, N.v56961.
  unfold R.v6, N.v6.
  rewrite ?node_56960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56962 (s : N.State) (i : N.Inputs) :
  R.v56962 (state s) (inputs i) = Zmod.unsigned (N.v56962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56962 s i)) at 1.
  unfold R.v56962, N.v56962.
  rewrite ?node_14358.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56963 (s : N.State) (i : N.Inputs) :
  R.v56963 (state s) (inputs i) = Zmod.unsigned (N.v56963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56963 s i)) at 1.
  unfold R.v56963, N.v56963.
  unfold R.v6, N.v6.
  rewrite ?node_14452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56964 (s : N.State) (i : N.Inputs) :
  R.v56964 (state s) (inputs i) = Zmod.unsigned (N.v56964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56964 s i)) at 1.
  unfold R.v56964, N.v56964.
  unfold R.v6, N.v6.
  rewrite ?node_14456.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56965 (s : N.State) (i : N.Inputs) :
  R.v56965 (state s) (inputs i) = Zmod.unsigned (N.v56965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56965 s i)) at 1.
  unfold R.v56965, N.v56965.
  rewrite ?node_56962.
  rewrite ?node_56963.
  rewrite ?node_56964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56966 (s : N.State) (i : N.Inputs) :
  R.v56966 (state s) (inputs i) = Zmod.unsigned (N.v56966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56966 s i)) at 1.
  unfold R.v56966, N.v56966.
  rewrite ?node_56961.
  rewrite ?node_56965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56967 (s : N.State) (i : N.Inputs) :
  R.v56967 (state s) (inputs i) = Zmod.unsigned (N.v56967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56967 s i)) at 1.
  unfold R.v56967, N.v56967.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56968 (s : N.State) (i : N.Inputs) :
  R.v56968 (state s) (inputs i) = Zmod.unsigned (N.v56968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56968 s i)) at 1.
  unfold R.v56968, N.v56968.
  rewrite ?node_14351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56969 (s : N.State) (i : N.Inputs) :
  R.v56969 (state s) (inputs i) = Zmod.unsigned (N.v56969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56969 s i)) at 1.
  unfold R.v56969, N.v56969.
  unfold R.v6, N.v6.
  rewrite ?node_14347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56970 (s : N.State) (i : N.Inputs) :
  R.v56970 (state s) (inputs i) = Zmod.unsigned (N.v56970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56970 s i)) at 1.
  unfold R.v56970, N.v56970.
  unfold R.v6, N.v6.
  rewrite ?node_14342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56971 (s : N.State) (i : N.Inputs) :
  R.v56971 (state s) (inputs i) = Zmod.unsigned (N.v56971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56971 s i)) at 1.
  unfold R.v56971, N.v56971.
  rewrite ?node_56969.
  rewrite ?node_56970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56972 (s : N.State) (i : N.Inputs) :
  R.v56972 (state s) (inputs i) = Zmod.unsigned (N.v56972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56972 s i)) at 1.
  unfold R.v56972, N.v56972.
  unfold R.v16484, N.v16484.
  rewrite ?node_56971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56973 (s : N.State) (i : N.Inputs) :
  R.v56973 (state s) (inputs i) = Zmod.unsigned (N.v56973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56973 s i)) at 1.
  unfold R.v56973, N.v56973.
  rewrite ?node_56968.
  rewrite ?node_56972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56974 (s : N.State) (i : N.Inputs) :
  R.v56974 (state s) (inputs i) = Zmod.unsigned (N.v56974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56974 s i)) at 1.
  unfold R.v56974, N.v56974.
  unfold R.v6, N.v6.
  rewrite ?node_56973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56975 (s : N.State) (i : N.Inputs) :
  R.v56975 (state s) (inputs i) = Zmod.unsigned (N.v56975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56975 s i)) at 1.
  unfold R.v56975, N.v56975.
  rewrite ?node_14352.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56976 (s : N.State) (i : N.Inputs) :
  R.v56976 (state s) (inputs i) = Zmod.unsigned (N.v56976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56976 s i)) at 1.
  unfold R.v56976, N.v56976.
  unfold R.v6, N.v6.
  rewrite ?node_14452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56977 (s : N.State) (i : N.Inputs) :
  R.v56977 (state s) (inputs i) = Zmod.unsigned (N.v56977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56977 s i)) at 1.
  unfold R.v56977, N.v56977.
  rewrite ?node_56975.
  rewrite ?node_56976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56978 (s : N.State) (i : N.Inputs) :
  R.v56978 (state s) (inputs i) = Zmod.unsigned (N.v56978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56978 s i)) at 1.
  unfold R.v56978, N.v56978.
  rewrite ?node_56974.
  rewrite ?node_56977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56979 (s : N.State) (i : N.Inputs) :
  R.v56979 (state s) (inputs i) = Zmod.unsigned (N.v56979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56979 s i)) at 1.
  unfold R.v56979, N.v56979.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56980 (s : N.State) (i : N.Inputs) :
  R.v56980 (state s) (inputs i) = Zmod.unsigned (N.v56980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56980 s i)) at 1.
  unfold R.v56980, N.v56980.
  rewrite ?node_14357.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56981 (s : N.State) (i : N.Inputs) :
  R.v56981 (state s) (inputs i) = Zmod.unsigned (N.v56981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56981 s i)) at 1.
  unfold R.v56981, N.v56981.
  unfold R.v6, N.v6.
  rewrite ?node_14353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56982 (s : N.State) (i : N.Inputs) :
  R.v56982 (state s) (inputs i) = Zmod.unsigned (N.v56982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56982 s i)) at 1.
  unfold R.v56982, N.v56982.
  unfold R.v6, N.v6.
  rewrite ?node_14352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56983 (s : N.State) (i : N.Inputs) :
  R.v56983 (state s) (inputs i) = Zmod.unsigned (N.v56983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56983 s i)) at 1.
  unfold R.v56983, N.v56983.
  rewrite ?node_56981.
  rewrite ?node_56982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56984 (s : N.State) (i : N.Inputs) :
  R.v56984 (state s) (inputs i) = Zmod.unsigned (N.v56984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56984 s i)) at 1.
  unfold R.v56984, N.v56984.
  unfold R.v16484, N.v16484.
  rewrite ?node_56983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56985 (s : N.State) (i : N.Inputs) :
  R.v56985 (state s) (inputs i) = Zmod.unsigned (N.v56985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56985 s i)) at 1.
  unfold R.v56985, N.v56985.
  rewrite ?node_56980.
  rewrite ?node_56984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56986 (s : N.State) (i : N.Inputs) :
  R.v56986 (state s) (inputs i) = Zmod.unsigned (N.v56986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56986 s i)) at 1.
  unfold R.v56986, N.v56986.
  unfold R.v6, N.v6.
  rewrite ?node_56985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56987 (s : N.State) (i : N.Inputs) :
  R.v56987 (state s) (inputs i) = Zmod.unsigned (N.v56987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56987 s i)) at 1.
  unfold R.v56987, N.v56987.
  rewrite ?node_14358.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56988 (s : N.State) (i : N.Inputs) :
  R.v56988 (state s) (inputs i) = Zmod.unsigned (N.v56988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56988 s i)) at 1.
  unfold R.v56988, N.v56988.
  unfold R.v6, N.v6.
  rewrite ?node_14456.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56989 (s : N.State) (i : N.Inputs) :
  R.v56989 (state s) (inputs i) = Zmod.unsigned (N.v56989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56989 s i)) at 1.
  unfold R.v56989, N.v56989.
  rewrite ?node_56987.
  rewrite ?node_56988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56990 (s : N.State) (i : N.Inputs) :
  R.v56990 (state s) (inputs i) = Zmod.unsigned (N.v56990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56990 s i)) at 1.
  unfold R.v56990, N.v56990.
  rewrite ?node_56986.
  rewrite ?node_56989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56991 (s : N.State) (i : N.Inputs) :
  R.v56991 (state s) (inputs i) = Zmod.unsigned (N.v56991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56991 s i)) at 1.
  unfold R.v56991, N.v56991.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56992 (s : N.State) (i : N.Inputs) :
  R.v56992 (state s) (inputs i) = Zmod.unsigned (N.v56992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56992 s i)) at 1.
  unfold R.v56992, N.v56992.
  rewrite ?node_14452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56993 (s : N.State) (i : N.Inputs) :
  R.v56993 (state s) (inputs i) = Zmod.unsigned (N.v56993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56993 s i)) at 1.
  unfold R.v56993, N.v56993.
  rewrite ?node_14448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56994 (s : N.State) (i : N.Inputs) :
  R.v56994 (state s) (inputs i) = Zmod.unsigned (N.v56994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56994 s i)) at 1.
  unfold R.v56994, N.v56994.
  rewrite ?node_14446.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56995 (s : N.State) (i : N.Inputs) :
  R.v56995 (state s) (inputs i) = Zmod.unsigned (N.v56995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56995 s i)) at 1.
  unfold R.v56995, N.v56995.
  unfold R.v6, N.v6.
  rewrite ?node_14442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56996 (s : N.State) (i : N.Inputs) :
  R.v56996 (state s) (inputs i) = Zmod.unsigned (N.v56996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56996 s i)) at 1.
  unfold R.v56996, N.v56996.
  unfold R.v6, N.v6.
  rewrite ?node_14435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56997 (s : N.State) (i : N.Inputs) :
  R.v56997 (state s) (inputs i) = Zmod.unsigned (N.v56997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56997 s i)) at 1.
  unfold R.v56997, N.v56997.
  rewrite ?node_56995.
  rewrite ?node_56996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56998 (s : N.State) (i : N.Inputs) :
  R.v56998 (state s) (inputs i) = Zmod.unsigned (N.v56998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56998 s i)) at 1.
  unfold R.v56998, N.v56998.
  unfold R.v16484, N.v16484.
  rewrite ?node_56997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56999 (s : N.State) (i : N.Inputs) :
  R.v56999 (state s) (inputs i) = Zmod.unsigned (N.v56999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56999 s i)) at 1.
  unfold R.v56999, N.v56999.
  rewrite ?node_56992.
  rewrite ?node_56993.
  rewrite ?node_56994.
  rewrite ?node_56998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
