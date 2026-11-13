(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes046.
Lemma node_47000 (s : N.State) (i : N.Inputs) :
  R.v47000 (state s) (inputs i) = Zmod.unsigned (N.v47000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47000 s i)) at 1.
  unfold R.v47000, N.v47000.
  rewrite ?node_46998.
  rewrite ?node_46999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47001 (s : N.State) (i : N.Inputs) :
  R.v47001 (state s) (inputs i) = Zmod.unsigned (N.v47001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47001 s i)) at 1.
  unfold R.v47001, N.v47001.
  rewrite ?node_46997.
  rewrite ?node_47000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47002 (s : N.State) (i : N.Inputs) :
  R.v47002 (state s) (inputs i) = Zmod.unsigned (N.v47002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47002 s i)) at 1.
  unfold R.v47002, N.v47002.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47003 (s : N.State) (i : N.Inputs) :
  R.v47003 (state s) (inputs i) = Zmod.unsigned (N.v47003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47003 s i)) at 1.
  unfold R.v47003, N.v47003.
  unfold R.v6, N.v6.
  rewrite ?node_14518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47004 (s : N.State) (i : N.Inputs) :
  R.v47004 (state s) (inputs i) = Zmod.unsigned (N.v47004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47004 s i)) at 1.
  unfold R.v47004, N.v47004.
  unfold R.v6, N.v6.
  rewrite ?node_14515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47005 (s : N.State) (i : N.Inputs) :
  R.v47005 (state s) (inputs i) = Zmod.unsigned (N.v47005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47005 s i)) at 1.
  unfold R.v47005, N.v47005.
  rewrite ?node_47003.
  rewrite ?node_47004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47006 (s : N.State) (i : N.Inputs) :
  R.v47006 (state s) (inputs i) = Zmod.unsigned (N.v47006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47006 s i)) at 1.
  unfold R.v47006, N.v47006.
  unfold R.v16463, N.v16463.
  rewrite ?node_47005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47007 (s : N.State) (i : N.Inputs) :
  R.v47007 (state s) (inputs i) = Zmod.unsigned (N.v47007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47007 s i)) at 1.
  unfold R.v47007, N.v47007.
  rewrite ?node_14519.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47008 (s : N.State) (i : N.Inputs) :
  R.v47008 (state s) (inputs i) = Zmod.unsigned (N.v47008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47008 s i)) at 1.
  unfold R.v47008, N.v47008.
  unfold R.v6, N.v6.
  rewrite ?node_14622.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47009 (s : N.State) (i : N.Inputs) :
  R.v47009 (state s) (inputs i) = Zmod.unsigned (N.v47009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47009 s i)) at 1.
  unfold R.v47009, N.v47009.
  rewrite ?node_47007.
  rewrite ?node_47008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47010 (s : N.State) (i : N.Inputs) :
  R.v47010 (state s) (inputs i) = Zmod.unsigned (N.v47010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47010 s i)) at 1.
  unfold R.v47010, N.v47010.
  rewrite ?node_47006.
  rewrite ?node_47009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47011 (s : N.State) (i : N.Inputs) :
  R.v47011 (state s) (inputs i) = Zmod.unsigned (N.v47011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47011 s i)) at 1.
  unfold R.v47011, N.v47011.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47012 (s : N.State) (i : N.Inputs) :
  R.v47012 (state s) (inputs i) = Zmod.unsigned (N.v47012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47012 s i)) at 1.
  unfold R.v47012, N.v47012.
  rewrite ?node_14585.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47013 (s : N.State) (i : N.Inputs) :
  R.v47013 (state s) (inputs i) = Zmod.unsigned (N.v47013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47013 s i)) at 1.
  unfold R.v47013, N.v47013.
  rewrite ?node_14581.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47014 (s : N.State) (i : N.Inputs) :
  R.v47014 (state s) (inputs i) = Zmod.unsigned (N.v47014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47014 s i)) at 1.
  unfold R.v47014, N.v47014.
  rewrite ?node_14573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47015 (s : N.State) (i : N.Inputs) :
  R.v47015 (state s) (inputs i) = Zmod.unsigned (N.v47015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47015 s i)) at 1.
  unfold R.v47015, N.v47015.
  unfold R.v6, N.v6.
  rewrite ?node_14565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47016 (s : N.State) (i : N.Inputs) :
  R.v47016 (state s) (inputs i) = Zmod.unsigned (N.v47016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47016 s i)) at 1.
  unfold R.v47016, N.v47016.
  unfold R.v6, N.v6.
  rewrite ?node_14558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47017 (s : N.State) (i : N.Inputs) :
  R.v47017 (state s) (inputs i) = Zmod.unsigned (N.v47017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47017 s i)) at 1.
  unfold R.v47017, N.v47017.
  rewrite ?node_47015.
  rewrite ?node_47016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47018 (s : N.State) (i : N.Inputs) :
  R.v47018 (state s) (inputs i) = Zmod.unsigned (N.v47018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47018 s i)) at 1.
  unfold R.v47018, N.v47018.
  unfold R.v16484, N.v16484.
  rewrite ?node_47017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47019 (s : N.State) (i : N.Inputs) :
  R.v47019 (state s) (inputs i) = Zmod.unsigned (N.v47019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47019 s i)) at 1.
  unfold R.v47019, N.v47019.
  rewrite ?node_47012.
  rewrite ?node_47013.
  rewrite ?node_47014.
  rewrite ?node_47018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47020 (s : N.State) (i : N.Inputs) :
  R.v47020 (state s) (inputs i) = Zmod.unsigned (N.v47020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47020 s i)) at 1.
  unfold R.v47020, N.v47020.
  unfold R.v6, N.v6.
  rewrite ?node_47019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47021 (s : N.State) (i : N.Inputs) :
  R.v47021 (state s) (inputs i) = Zmod.unsigned (N.v47021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47021 s i)) at 1.
  unfold R.v47021, N.v47021.
  rewrite ?node_14586.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47022 (s : N.State) (i : N.Inputs) :
  R.v47022 (state s) (inputs i) = Zmod.unsigned (N.v47022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47022 s i)) at 1.
  unfold R.v47022, N.v47022.
  unfold R.v6, N.v6.
  rewrite ?node_14674.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47023 (s : N.State) (i : N.Inputs) :
  R.v47023 (state s) (inputs i) = Zmod.unsigned (N.v47023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47023 s i)) at 1.
  unfold R.v47023, N.v47023.
  unfold R.v6, N.v6.
  rewrite ?node_14701.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47024 (s : N.State) (i : N.Inputs) :
  R.v47024 (state s) (inputs i) = Zmod.unsigned (N.v47024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47024 s i)) at 1.
  unfold R.v47024, N.v47024.
  rewrite ?node_47021.
  rewrite ?node_47022.
  rewrite ?node_47023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47025 (s : N.State) (i : N.Inputs) :
  R.v47025 (state s) (inputs i) = Zmod.unsigned (N.v47025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47025 s i)) at 1.
  unfold R.v47025, N.v47025.
  rewrite ?node_47020.
  rewrite ?node_47024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47026 (s : N.State) (i : N.Inputs) :
  R.v47026 (state s) (inputs i) = Zmod.unsigned (N.v47026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47026 s i)) at 1.
  unfold R.v47026, N.v47026.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47027 (s : N.State) (i : N.Inputs) :
  R.v47027 (state s) (inputs i) = Zmod.unsigned (N.v47027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47027 s i)) at 1.
  unfold R.v47027, N.v47027.
  rewrite ?node_14573.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47028 (s : N.State) (i : N.Inputs) :
  R.v47028 (state s) (inputs i) = Zmod.unsigned (N.v47028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47028 s i)) at 1.
  unfold R.v47028, N.v47028.
  unfold R.v6, N.v6.
  rewrite ?node_14565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47029 (s : N.State) (i : N.Inputs) :
  R.v47029 (state s) (inputs i) = Zmod.unsigned (N.v47029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47029 s i)) at 1.
  unfold R.v47029, N.v47029.
  unfold R.v6, N.v6.
  rewrite ?node_14558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47030 (s : N.State) (i : N.Inputs) :
  R.v47030 (state s) (inputs i) = Zmod.unsigned (N.v47030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47030 s i)) at 1.
  unfold R.v47030, N.v47030.
  rewrite ?node_47028.
  rewrite ?node_47029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47031 (s : N.State) (i : N.Inputs) :
  R.v47031 (state s) (inputs i) = Zmod.unsigned (N.v47031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47031 s i)) at 1.
  unfold R.v47031, N.v47031.
  unfold R.v16484, N.v16484.
  rewrite ?node_47030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47032 (s : N.State) (i : N.Inputs) :
  R.v47032 (state s) (inputs i) = Zmod.unsigned (N.v47032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47032 s i)) at 1.
  unfold R.v47032, N.v47032.
  rewrite ?node_47027.
  rewrite ?node_47031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47033 (s : N.State) (i : N.Inputs) :
  R.v47033 (state s) (inputs i) = Zmod.unsigned (N.v47033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47033 s i)) at 1.
  unfold R.v47033, N.v47033.
  unfold R.v6, N.v6.
  rewrite ?node_47032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47034 (s : N.State) (i : N.Inputs) :
  R.v47034 (state s) (inputs i) = Zmod.unsigned (N.v47034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47034 s i)) at 1.
  unfold R.v47034, N.v47034.
  rewrite ?node_14574.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47035 (s : N.State) (i : N.Inputs) :
  R.v47035 (state s) (inputs i) = Zmod.unsigned (N.v47035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47035 s i)) at 1.
  unfold R.v47035, N.v47035.
  unfold R.v6, N.v6.
  rewrite ?node_14674.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47036 (s : N.State) (i : N.Inputs) :
  R.v47036 (state s) (inputs i) = Zmod.unsigned (N.v47036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47036 s i)) at 1.
  unfold R.v47036, N.v47036.
  rewrite ?node_47034.
  rewrite ?node_47035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47037 (s : N.State) (i : N.Inputs) :
  R.v47037 (state s) (inputs i) = Zmod.unsigned (N.v47037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47037 s i)) at 1.
  unfold R.v47037, N.v47037.
  rewrite ?node_47033.
  rewrite ?node_47036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47038 (s : N.State) (i : N.Inputs) :
  R.v47038 (state s) (inputs i) = Zmod.unsigned (N.v47038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47038 s i)) at 1.
  unfold R.v47038, N.v47038.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47039 (s : N.State) (i : N.Inputs) :
  R.v47039 (state s) (inputs i) = Zmod.unsigned (N.v47039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47039 s i)) at 1.
  unfold R.v47039, N.v47039.
  rewrite ?node_14585.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47040 (s : N.State) (i : N.Inputs) :
  R.v47040 (state s) (inputs i) = Zmod.unsigned (N.v47040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47040 s i)) at 1.
  unfold R.v47040, N.v47040.
  unfold R.v6, N.v6.
  rewrite ?node_14581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47041 (s : N.State) (i : N.Inputs) :
  R.v47041 (state s) (inputs i) = Zmod.unsigned (N.v47041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47041 s i)) at 1.
  unfold R.v47041, N.v47041.
  unfold R.v6, N.v6.
  rewrite ?node_14574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47042 (s : N.State) (i : N.Inputs) :
  R.v47042 (state s) (inputs i) = Zmod.unsigned (N.v47042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47042 s i)) at 1.
  unfold R.v47042, N.v47042.
  rewrite ?node_47040.
  rewrite ?node_47041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47043 (s : N.State) (i : N.Inputs) :
  R.v47043 (state s) (inputs i) = Zmod.unsigned (N.v47043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47043 s i)) at 1.
  unfold R.v47043, N.v47043.
  unfold R.v16484, N.v16484.
  rewrite ?node_47042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47044 (s : N.State) (i : N.Inputs) :
  R.v47044 (state s) (inputs i) = Zmod.unsigned (N.v47044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47044 s i)) at 1.
  unfold R.v47044, N.v47044.
  rewrite ?node_47039.
  rewrite ?node_47043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47045 (s : N.State) (i : N.Inputs) :
  R.v47045 (state s) (inputs i) = Zmod.unsigned (N.v47045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47045 s i)) at 1.
  unfold R.v47045, N.v47045.
  unfold R.v6, N.v6.
  rewrite ?node_47044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47046 (s : N.State) (i : N.Inputs) :
  R.v47046 (state s) (inputs i) = Zmod.unsigned (N.v47046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47046 s i)) at 1.
  unfold R.v47046, N.v47046.
  rewrite ?node_14586.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47047 (s : N.State) (i : N.Inputs) :
  R.v47047 (state s) (inputs i) = Zmod.unsigned (N.v47047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47047 s i)) at 1.
  unfold R.v47047, N.v47047.
  unfold R.v6, N.v6.
  rewrite ?node_14701.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47048 (s : N.State) (i : N.Inputs) :
  R.v47048 (state s) (inputs i) = Zmod.unsigned (N.v47048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47048 s i)) at 1.
  unfold R.v47048, N.v47048.
  rewrite ?node_47046.
  rewrite ?node_47047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47049 (s : N.State) (i : N.Inputs) :
  R.v47049 (state s) (inputs i) = Zmod.unsigned (N.v47049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47049 s i)) at 1.
  unfold R.v47049, N.v47049.
  rewrite ?node_47045.
  rewrite ?node_47048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47050 (s : N.State) (i : N.Inputs) :
  R.v47050 (state s) (inputs i) = Zmod.unsigned (N.v47050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47050 s i)) at 1.
  unfold R.v47050, N.v47050.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47051 (s : N.State) (i : N.Inputs) :
  R.v47051 (state s) (inputs i) = Zmod.unsigned (N.v47051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47051 s i)) at 1.
  unfold R.v47051, N.v47051.
  rewrite ?node_14602.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47052 (s : N.State) (i : N.Inputs) :
  R.v47052 (state s) (inputs i) = Zmod.unsigned (N.v47052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47052 s i)) at 1.
  unfold R.v47052, N.v47052.
  rewrite ?node_14598.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47053 (s : N.State) (i : N.Inputs) :
  R.v47053 (state s) (inputs i) = Zmod.unsigned (N.v47053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47053 s i)) at 1.
  unfold R.v47053, N.v47053.
  rewrite ?node_14594.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47054 (s : N.State) (i : N.Inputs) :
  R.v47054 (state s) (inputs i) = Zmod.unsigned (N.v47054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47054 s i)) at 1.
  unfold R.v47054, N.v47054.
  unfold R.v6, N.v6.
  rewrite ?node_14590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47055 (s : N.State) (i : N.Inputs) :
  R.v47055 (state s) (inputs i) = Zmod.unsigned (N.v47055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47055 s i)) at 1.
  unfold R.v47055, N.v47055.
  unfold R.v6, N.v6.
  rewrite ?node_14587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47056 (s : N.State) (i : N.Inputs) :
  R.v47056 (state s) (inputs i) = Zmod.unsigned (N.v47056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47056 s i)) at 1.
  unfold R.v47056, N.v47056.
  rewrite ?node_47054.
  rewrite ?node_47055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47057 (s : N.State) (i : N.Inputs) :
  R.v47057 (state s) (inputs i) = Zmod.unsigned (N.v47057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47057 s i)) at 1.
  unfold R.v47057, N.v47057.
  unfold R.v16484, N.v16484.
  rewrite ?node_47056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47058 (s : N.State) (i : N.Inputs) :
  R.v47058 (state s) (inputs i) = Zmod.unsigned (N.v47058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47058 s i)) at 1.
  unfold R.v47058, N.v47058.
  rewrite ?node_47051.
  rewrite ?node_47052.
  rewrite ?node_47053.
  rewrite ?node_47057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47059 (s : N.State) (i : N.Inputs) :
  R.v47059 (state s) (inputs i) = Zmod.unsigned (N.v47059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47059 s i)) at 1.
  unfold R.v47059, N.v47059.
  unfold R.v6, N.v6.
  rewrite ?node_47058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47060 (s : N.State) (i : N.Inputs) :
  R.v47060 (state s) (inputs i) = Zmod.unsigned (N.v47060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47060 s i)) at 1.
  unfold R.v47060, N.v47060.
  rewrite ?node_14603.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47061 (s : N.State) (i : N.Inputs) :
  R.v47061 (state s) (inputs i) = Zmod.unsigned (N.v47061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47061 s i)) at 1.
  unfold R.v47061, N.v47061.
  unfold R.v6, N.v6.
  rewrite ?node_14690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47062 (s : N.State) (i : N.Inputs) :
  R.v47062 (state s) (inputs i) = Zmod.unsigned (N.v47062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47062 s i)) at 1.
  unfold R.v47062, N.v47062.
  unfold R.v6, N.v6.
  rewrite ?node_14709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47063 (s : N.State) (i : N.Inputs) :
  R.v47063 (state s) (inputs i) = Zmod.unsigned (N.v47063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47063 s i)) at 1.
  unfold R.v47063, N.v47063.
  rewrite ?node_47060.
  rewrite ?node_47061.
  rewrite ?node_47062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47064 (s : N.State) (i : N.Inputs) :
  R.v47064 (state s) (inputs i) = Zmod.unsigned (N.v47064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47064 s i)) at 1.
  unfold R.v47064, N.v47064.
  rewrite ?node_47059.
  rewrite ?node_47063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47065 (s : N.State) (i : N.Inputs) :
  R.v47065 (state s) (inputs i) = Zmod.unsigned (N.v47065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47065 s i)) at 1.
  unfold R.v47065, N.v47065.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47066 (s : N.State) (i : N.Inputs) :
  R.v47066 (state s) (inputs i) = Zmod.unsigned (N.v47066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47066 s i)) at 1.
  unfold R.v47066, N.v47066.
  rewrite ?node_14594.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47067 (s : N.State) (i : N.Inputs) :
  R.v47067 (state s) (inputs i) = Zmod.unsigned (N.v47067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47067 s i)) at 1.
  unfold R.v47067, N.v47067.
  unfold R.v6, N.v6.
  rewrite ?node_14590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47068 (s : N.State) (i : N.Inputs) :
  R.v47068 (state s) (inputs i) = Zmod.unsigned (N.v47068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47068 s i)) at 1.
  unfold R.v47068, N.v47068.
  unfold R.v6, N.v6.
  rewrite ?node_14587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47069 (s : N.State) (i : N.Inputs) :
  R.v47069 (state s) (inputs i) = Zmod.unsigned (N.v47069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47069 s i)) at 1.
  unfold R.v47069, N.v47069.
  rewrite ?node_47067.
  rewrite ?node_47068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47070 (s : N.State) (i : N.Inputs) :
  R.v47070 (state s) (inputs i) = Zmod.unsigned (N.v47070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47070 s i)) at 1.
  unfold R.v47070, N.v47070.
  unfold R.v16484, N.v16484.
  rewrite ?node_47069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47071 (s : N.State) (i : N.Inputs) :
  R.v47071 (state s) (inputs i) = Zmod.unsigned (N.v47071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47071 s i)) at 1.
  unfold R.v47071, N.v47071.
  rewrite ?node_47066.
  rewrite ?node_47070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47072 (s : N.State) (i : N.Inputs) :
  R.v47072 (state s) (inputs i) = Zmod.unsigned (N.v47072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47072 s i)) at 1.
  unfold R.v47072, N.v47072.
  unfold R.v6, N.v6.
  rewrite ?node_47071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47073 (s : N.State) (i : N.Inputs) :
  R.v47073 (state s) (inputs i) = Zmod.unsigned (N.v47073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47073 s i)) at 1.
  unfold R.v47073, N.v47073.
  rewrite ?node_14595.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47074 (s : N.State) (i : N.Inputs) :
  R.v47074 (state s) (inputs i) = Zmod.unsigned (N.v47074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47074 s i)) at 1.
  unfold R.v47074, N.v47074.
  unfold R.v6, N.v6.
  rewrite ?node_14690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47075 (s : N.State) (i : N.Inputs) :
  R.v47075 (state s) (inputs i) = Zmod.unsigned (N.v47075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47075 s i)) at 1.
  unfold R.v47075, N.v47075.
  rewrite ?node_47073.
  rewrite ?node_47074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47076 (s : N.State) (i : N.Inputs) :
  R.v47076 (state s) (inputs i) = Zmod.unsigned (N.v47076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47076 s i)) at 1.
  unfold R.v47076, N.v47076.
  rewrite ?node_47072.
  rewrite ?node_47075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47077 (s : N.State) (i : N.Inputs) :
  R.v47077 (state s) (inputs i) = Zmod.unsigned (N.v47077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47077 s i)) at 1.
  unfold R.v47077, N.v47077.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47078 (s : N.State) (i : N.Inputs) :
  R.v47078 (state s) (inputs i) = Zmod.unsigned (N.v47078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47078 s i)) at 1.
  unfold R.v47078, N.v47078.
  rewrite ?node_14602.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47079 (s : N.State) (i : N.Inputs) :
  R.v47079 (state s) (inputs i) = Zmod.unsigned (N.v47079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47079 s i)) at 1.
  unfold R.v47079, N.v47079.
  unfold R.v6, N.v6.
  rewrite ?node_14598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47080 (s : N.State) (i : N.Inputs) :
  R.v47080 (state s) (inputs i) = Zmod.unsigned (N.v47080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47080 s i)) at 1.
  unfold R.v47080, N.v47080.
  unfold R.v6, N.v6.
  rewrite ?node_14595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47081 (s : N.State) (i : N.Inputs) :
  R.v47081 (state s) (inputs i) = Zmod.unsigned (N.v47081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47081 s i)) at 1.
  unfold R.v47081, N.v47081.
  rewrite ?node_47079.
  rewrite ?node_47080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47082 (s : N.State) (i : N.Inputs) :
  R.v47082 (state s) (inputs i) = Zmod.unsigned (N.v47082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47082 s i)) at 1.
  unfold R.v47082, N.v47082.
  unfold R.v16484, N.v16484.
  rewrite ?node_47081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47083 (s : N.State) (i : N.Inputs) :
  R.v47083 (state s) (inputs i) = Zmod.unsigned (N.v47083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47083 s i)) at 1.
  unfold R.v47083, N.v47083.
  rewrite ?node_47078.
  rewrite ?node_47082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47084 (s : N.State) (i : N.Inputs) :
  R.v47084 (state s) (inputs i) = Zmod.unsigned (N.v47084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47084 s i)) at 1.
  unfold R.v47084, N.v47084.
  unfold R.v6, N.v6.
  rewrite ?node_47083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47085 (s : N.State) (i : N.Inputs) :
  R.v47085 (state s) (inputs i) = Zmod.unsigned (N.v47085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47085 s i)) at 1.
  unfold R.v47085, N.v47085.
  rewrite ?node_14603.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47086 (s : N.State) (i : N.Inputs) :
  R.v47086 (state s) (inputs i) = Zmod.unsigned (N.v47086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47086 s i)) at 1.
  unfold R.v47086, N.v47086.
  unfold R.v6, N.v6.
  rewrite ?node_14709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47087 (s : N.State) (i : N.Inputs) :
  R.v47087 (state s) (inputs i) = Zmod.unsigned (N.v47087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47087 s i)) at 1.
  unfold R.v47087, N.v47087.
  rewrite ?node_47085.
  rewrite ?node_47086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47088 (s : N.State) (i : N.Inputs) :
  R.v47088 (state s) (inputs i) = Zmod.unsigned (N.v47088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47088 s i)) at 1.
  unfold R.v47088, N.v47088.
  rewrite ?node_47084.
  rewrite ?node_47087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47089 (s : N.State) (i : N.Inputs) :
  R.v47089 (state s) (inputs i) = Zmod.unsigned (N.v47089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47089 s i)) at 1.
  unfold R.v47089, N.v47089.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47090 (s : N.State) (i : N.Inputs) :
  R.v47090 (state s) (inputs i) = Zmod.unsigned (N.v47090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47090 s i)) at 1.
  unfold R.v47090, N.v47090.
  unfold R.v6, N.v6.
  rewrite ?node_14608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47091 (s : N.State) (i : N.Inputs) :
  R.v47091 (state s) (inputs i) = Zmod.unsigned (N.v47091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47091 s i)) at 1.
  unfold R.v47091, N.v47091.
  unfold R.v6, N.v6.
  rewrite ?node_14607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47092 (s : N.State) (i : N.Inputs) :
  R.v47092 (state s) (inputs i) = Zmod.unsigned (N.v47092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47092 s i)) at 1.
  unfold R.v47092, N.v47092.
  rewrite ?node_47090.
  rewrite ?node_47091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47093 (s : N.State) (i : N.Inputs) :
  R.v47093 (state s) (inputs i) = Zmod.unsigned (N.v47093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47093 s i)) at 1.
  unfold R.v47093, N.v47093.
  unfold R.v16463, N.v16463.
  rewrite ?node_47092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47094 (s : N.State) (i : N.Inputs) :
  R.v47094 (state s) (inputs i) = Zmod.unsigned (N.v47094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47094 s i)) at 1.
  unfold R.v47094, N.v47094.
  rewrite ?node_14609.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47095 (s : N.State) (i : N.Inputs) :
  R.v47095 (state s) (inputs i) = Zmod.unsigned (N.v47095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47095 s i)) at 1.
  unfold R.v47095, N.v47095.
  unfold R.v6, N.v6.
  rewrite ?node_14710.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47096 (s : N.State) (i : N.Inputs) :
  R.v47096 (state s) (inputs i) = Zmod.unsigned (N.v47096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47096 s i)) at 1.
  unfold R.v47096, N.v47096.
  rewrite ?node_47094.
  rewrite ?node_47095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47097 (s : N.State) (i : N.Inputs) :
  R.v47097 (state s) (inputs i) = Zmod.unsigned (N.v47097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47097 s i)) at 1.
  unfold R.v47097, N.v47097.
  rewrite ?node_47093.
  rewrite ?node_47096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47098 (s : N.State) (i : N.Inputs) :
  R.v47098 (state s) (inputs i) = Zmod.unsigned (N.v47098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47098 s i)) at 1.
  unfold R.v47098, N.v47098.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47099 (s : N.State) (i : N.Inputs) :
  R.v47099 (state s) (inputs i) = Zmod.unsigned (N.v47099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47099 s i)) at 1.
  unfold R.v47099, N.v47099.
  rewrite ?node_14674.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47100 (s : N.State) (i : N.Inputs) :
  R.v47100 (state s) (inputs i) = Zmod.unsigned (N.v47100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47100 s i)) at 1.
  unfold R.v47100, N.v47100.
  rewrite ?node_14670.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47101 (s : N.State) (i : N.Inputs) :
  R.v47101 (state s) (inputs i) = Zmod.unsigned (N.v47101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47101 s i)) at 1.
  unfold R.v47101, N.v47101.
  rewrite ?node_14662.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47102 (s : N.State) (i : N.Inputs) :
  R.v47102 (state s) (inputs i) = Zmod.unsigned (N.v47102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47102 s i)) at 1.
  unfold R.v47102, N.v47102.
  unfold R.v6, N.v6.
  rewrite ?node_14654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47103 (s : N.State) (i : N.Inputs) :
  R.v47103 (state s) (inputs i) = Zmod.unsigned (N.v47103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47103 s i)) at 1.
  unfold R.v47103, N.v47103.
  unfold R.v6, N.v6.
  rewrite ?node_14647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47104 (s : N.State) (i : N.Inputs) :
  R.v47104 (state s) (inputs i) = Zmod.unsigned (N.v47104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47104 s i)) at 1.
  unfold R.v47104, N.v47104.
  rewrite ?node_47102.
  rewrite ?node_47103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47105 (s : N.State) (i : N.Inputs) :
  R.v47105 (state s) (inputs i) = Zmod.unsigned (N.v47105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47105 s i)) at 1.
  unfold R.v47105, N.v47105.
  unfold R.v16484, N.v16484.
  rewrite ?node_47104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47106 (s : N.State) (i : N.Inputs) :
  R.v47106 (state s) (inputs i) = Zmod.unsigned (N.v47106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47106 s i)) at 1.
  unfold R.v47106, N.v47106.
  rewrite ?node_47099.
  rewrite ?node_47100.
  rewrite ?node_47101.
  rewrite ?node_47105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47107 (s : N.State) (i : N.Inputs) :
  R.v47107 (state s) (inputs i) = Zmod.unsigned (N.v47107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47107 s i)) at 1.
  unfold R.v47107, N.v47107.
  unfold R.v6, N.v6.
  rewrite ?node_47106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47108 (s : N.State) (i : N.Inputs) :
  R.v47108 (state s) (inputs i) = Zmod.unsigned (N.v47108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47108 s i)) at 1.
  unfold R.v47108, N.v47108.
  rewrite ?node_14675.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47109 (s : N.State) (i : N.Inputs) :
  R.v47109 (state s) (inputs i) = Zmod.unsigned (N.v47109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47109 s i)) at 1.
  unfold R.v47109, N.v47109.
  unfold R.v6, N.v6.
  rewrite ?node_14763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47110 (s : N.State) (i : N.Inputs) :
  R.v47110 (state s) (inputs i) = Zmod.unsigned (N.v47110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47110 s i)) at 1.
  unfold R.v47110, N.v47110.
  unfold R.v6, N.v6.
  rewrite ?node_14788.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47111 (s : N.State) (i : N.Inputs) :
  R.v47111 (state s) (inputs i) = Zmod.unsigned (N.v47111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47111 s i)) at 1.
  unfold R.v47111, N.v47111.
  rewrite ?node_47108.
  rewrite ?node_47109.
  rewrite ?node_47110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47112 (s : N.State) (i : N.Inputs) :
  R.v47112 (state s) (inputs i) = Zmod.unsigned (N.v47112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47112 s i)) at 1.
  unfold R.v47112, N.v47112.
  rewrite ?node_47107.
  rewrite ?node_47111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47113 (s : N.State) (i : N.Inputs) :
  R.v47113 (state s) (inputs i) = Zmod.unsigned (N.v47113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47113 s i)) at 1.
  unfold R.v47113, N.v47113.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47114 (s : N.State) (i : N.Inputs) :
  R.v47114 (state s) (inputs i) = Zmod.unsigned (N.v47114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47114 s i)) at 1.
  unfold R.v47114, N.v47114.
  rewrite ?node_14662.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47115 (s : N.State) (i : N.Inputs) :
  R.v47115 (state s) (inputs i) = Zmod.unsigned (N.v47115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47115 s i)) at 1.
  unfold R.v47115, N.v47115.
  unfold R.v6, N.v6.
  rewrite ?node_14654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47116 (s : N.State) (i : N.Inputs) :
  R.v47116 (state s) (inputs i) = Zmod.unsigned (N.v47116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47116 s i)) at 1.
  unfold R.v47116, N.v47116.
  unfold R.v6, N.v6.
  rewrite ?node_14647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47117 (s : N.State) (i : N.Inputs) :
  R.v47117 (state s) (inputs i) = Zmod.unsigned (N.v47117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47117 s i)) at 1.
  unfold R.v47117, N.v47117.
  rewrite ?node_47115.
  rewrite ?node_47116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47118 (s : N.State) (i : N.Inputs) :
  R.v47118 (state s) (inputs i) = Zmod.unsigned (N.v47118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47118 s i)) at 1.
  unfold R.v47118, N.v47118.
  unfold R.v16484, N.v16484.
  rewrite ?node_47117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47119 (s : N.State) (i : N.Inputs) :
  R.v47119 (state s) (inputs i) = Zmod.unsigned (N.v47119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47119 s i)) at 1.
  unfold R.v47119, N.v47119.
  rewrite ?node_47114.
  rewrite ?node_47118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47120 (s : N.State) (i : N.Inputs) :
  R.v47120 (state s) (inputs i) = Zmod.unsigned (N.v47120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47120 s i)) at 1.
  unfold R.v47120, N.v47120.
  unfold R.v6, N.v6.
  rewrite ?node_47119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47121 (s : N.State) (i : N.Inputs) :
  R.v47121 (state s) (inputs i) = Zmod.unsigned (N.v47121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47121 s i)) at 1.
  unfold R.v47121, N.v47121.
  rewrite ?node_14663.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47122 (s : N.State) (i : N.Inputs) :
  R.v47122 (state s) (inputs i) = Zmod.unsigned (N.v47122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47122 s i)) at 1.
  unfold R.v47122, N.v47122.
  unfold R.v6, N.v6.
  rewrite ?node_14763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47123 (s : N.State) (i : N.Inputs) :
  R.v47123 (state s) (inputs i) = Zmod.unsigned (N.v47123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47123 s i)) at 1.
  unfold R.v47123, N.v47123.
  rewrite ?node_47121.
  rewrite ?node_47122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47124 (s : N.State) (i : N.Inputs) :
  R.v47124 (state s) (inputs i) = Zmod.unsigned (N.v47124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47124 s i)) at 1.
  unfold R.v47124, N.v47124.
  rewrite ?node_47120.
  rewrite ?node_47123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47125 (s : N.State) (i : N.Inputs) :
  R.v47125 (state s) (inputs i) = Zmod.unsigned (N.v47125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47125 s i)) at 1.
  unfold R.v47125, N.v47125.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47126 (s : N.State) (i : N.Inputs) :
  R.v47126 (state s) (inputs i) = Zmod.unsigned (N.v47126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47126 s i)) at 1.
  unfold R.v47126, N.v47126.
  rewrite ?node_14674.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47127 (s : N.State) (i : N.Inputs) :
  R.v47127 (state s) (inputs i) = Zmod.unsigned (N.v47127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47127 s i)) at 1.
  unfold R.v47127, N.v47127.
  unfold R.v6, N.v6.
  rewrite ?node_14670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47128 (s : N.State) (i : N.Inputs) :
  R.v47128 (state s) (inputs i) = Zmod.unsigned (N.v47128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47128 s i)) at 1.
  unfold R.v47128, N.v47128.
  unfold R.v6, N.v6.
  rewrite ?node_14663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47129 (s : N.State) (i : N.Inputs) :
  R.v47129 (state s) (inputs i) = Zmod.unsigned (N.v47129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47129 s i)) at 1.
  unfold R.v47129, N.v47129.
  rewrite ?node_47127.
  rewrite ?node_47128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47130 (s : N.State) (i : N.Inputs) :
  R.v47130 (state s) (inputs i) = Zmod.unsigned (N.v47130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47130 s i)) at 1.
  unfold R.v47130, N.v47130.
  unfold R.v16484, N.v16484.
  rewrite ?node_47129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47131 (s : N.State) (i : N.Inputs) :
  R.v47131 (state s) (inputs i) = Zmod.unsigned (N.v47131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47131 s i)) at 1.
  unfold R.v47131, N.v47131.
  rewrite ?node_47126.
  rewrite ?node_47130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47132 (s : N.State) (i : N.Inputs) :
  R.v47132 (state s) (inputs i) = Zmod.unsigned (N.v47132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47132 s i)) at 1.
  unfold R.v47132, N.v47132.
  unfold R.v6, N.v6.
  rewrite ?node_47131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47133 (s : N.State) (i : N.Inputs) :
  R.v47133 (state s) (inputs i) = Zmod.unsigned (N.v47133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47133 s i)) at 1.
  unfold R.v47133, N.v47133.
  rewrite ?node_14675.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47134 (s : N.State) (i : N.Inputs) :
  R.v47134 (state s) (inputs i) = Zmod.unsigned (N.v47134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47134 s i)) at 1.
  unfold R.v47134, N.v47134.
  unfold R.v6, N.v6.
  rewrite ?node_14788.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47135 (s : N.State) (i : N.Inputs) :
  R.v47135 (state s) (inputs i) = Zmod.unsigned (N.v47135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47135 s i)) at 1.
  unfold R.v47135, N.v47135.
  rewrite ?node_47133.
  rewrite ?node_47134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47136 (s : N.State) (i : N.Inputs) :
  R.v47136 (state s) (inputs i) = Zmod.unsigned (N.v47136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47136 s i)) at 1.
  unfold R.v47136, N.v47136.
  rewrite ?node_47132.
  rewrite ?node_47135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47137 (s : N.State) (i : N.Inputs) :
  R.v47137 (state s) (inputs i) = Zmod.unsigned (N.v47137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47137 s i)) at 1.
  unfold R.v47137, N.v47137.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47138 (s : N.State) (i : N.Inputs) :
  R.v47138 (state s) (inputs i) = Zmod.unsigned (N.v47138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47138 s i)) at 1.
  unfold R.v47138, N.v47138.
  rewrite ?node_14690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47139 (s : N.State) (i : N.Inputs) :
  R.v47139 (state s) (inputs i) = Zmod.unsigned (N.v47139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47139 s i)) at 1.
  unfold R.v47139, N.v47139.
  rewrite ?node_14686.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47140 (s : N.State) (i : N.Inputs) :
  R.v47140 (state s) (inputs i) = Zmod.unsigned (N.v47140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47140 s i)) at 1.
  unfold R.v47140, N.v47140.
  rewrite ?node_14682.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47141 (s : N.State) (i : N.Inputs) :
  R.v47141 (state s) (inputs i) = Zmod.unsigned (N.v47141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47141 s i)) at 1.
  unfold R.v47141, N.v47141.
  unfold R.v6, N.v6.
  rewrite ?node_14678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47142 (s : N.State) (i : N.Inputs) :
  R.v47142 (state s) (inputs i) = Zmod.unsigned (N.v47142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47142 s i)) at 1.
  unfold R.v47142, N.v47142.
  unfold R.v6, N.v6.
  rewrite !state_r2006_nr_5F2021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2006_nr_5F2021 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47143 (s : N.State) (i : N.Inputs) :
  R.v47143 (state s) (inputs i) = Zmod.unsigned (N.v47143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47143 s i)) at 1.
  unfold R.v47143, N.v47143.
  rewrite ?node_47141.
  rewrite ?node_47142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47144 (s : N.State) (i : N.Inputs) :
  R.v47144 (state s) (inputs i) = Zmod.unsigned (N.v47144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47144 s i)) at 1.
  unfold R.v47144, N.v47144.
  unfold R.v16484, N.v16484.
  rewrite ?node_47143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47145 (s : N.State) (i : N.Inputs) :
  R.v47145 (state s) (inputs i) = Zmod.unsigned (N.v47145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47145 s i)) at 1.
  unfold R.v47145, N.v47145.
  rewrite ?node_47138.
  rewrite ?node_47139.
  rewrite ?node_47140.
  rewrite ?node_47144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47146 (s : N.State) (i : N.Inputs) :
  R.v47146 (state s) (inputs i) = Zmod.unsigned (N.v47146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47146 s i)) at 1.
  unfold R.v47146, N.v47146.
  unfold R.v6, N.v6.
  rewrite ?node_47145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47147 (s : N.State) (i : N.Inputs) :
  R.v47147 (state s) (inputs i) = Zmod.unsigned (N.v47147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47147 s i)) at 1.
  unfold R.v47147, N.v47147.
  rewrite ?node_14691.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47148 (s : N.State) (i : N.Inputs) :
  R.v47148 (state s) (inputs i) = Zmod.unsigned (N.v47148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47148 s i)) at 1.
  unfold R.v47148, N.v47148.
  unfold R.v6, N.v6.
  rewrite ?node_14779.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47149 (s : N.State) (i : N.Inputs) :
  R.v47149 (state s) (inputs i) = Zmod.unsigned (N.v47149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47149 s i)) at 1.
  unfold R.v47149, N.v47149.
  unfold R.v6, N.v6.
  rewrite ?node_14796.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47150 (s : N.State) (i : N.Inputs) :
  R.v47150 (state s) (inputs i) = Zmod.unsigned (N.v47150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47150 s i)) at 1.
  unfold R.v47150, N.v47150.
  rewrite ?node_47147.
  rewrite ?node_47148.
  rewrite ?node_47149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47151 (s : N.State) (i : N.Inputs) :
  R.v47151 (state s) (inputs i) = Zmod.unsigned (N.v47151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47151 s i)) at 1.
  unfold R.v47151, N.v47151.
  rewrite ?node_47146.
  rewrite ?node_47150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47152 (s : N.State) (i : N.Inputs) :
  R.v47152 (state s) (inputs i) = Zmod.unsigned (N.v47152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47152 s i)) at 1.
  unfold R.v47152, N.v47152.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47153 (s : N.State) (i : N.Inputs) :
  R.v47153 (state s) (inputs i) = Zmod.unsigned (N.v47153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47153 s i)) at 1.
  unfold R.v47153, N.v47153.
  rewrite ?node_14682.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47154 (s : N.State) (i : N.Inputs) :
  R.v47154 (state s) (inputs i) = Zmod.unsigned (N.v47154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47154 s i)) at 1.
  unfold R.v47154, N.v47154.
  unfold R.v6, N.v6.
  rewrite ?node_14678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47155 (s : N.State) (i : N.Inputs) :
  R.v47155 (state s) (inputs i) = Zmod.unsigned (N.v47155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47155 s i)) at 1.
  unfold R.v47155, N.v47155.
  unfold R.v6, N.v6.
  rewrite !state_r2006_nr_5F2021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2006_nr_5F2021 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47156 (s : N.State) (i : N.Inputs) :
  R.v47156 (state s) (inputs i) = Zmod.unsigned (N.v47156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47156 s i)) at 1.
  unfold R.v47156, N.v47156.
  rewrite ?node_47154.
  rewrite ?node_47155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47157 (s : N.State) (i : N.Inputs) :
  R.v47157 (state s) (inputs i) = Zmod.unsigned (N.v47157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47157 s i)) at 1.
  unfold R.v47157, N.v47157.
  unfold R.v16484, N.v16484.
  rewrite ?node_47156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47158 (s : N.State) (i : N.Inputs) :
  R.v47158 (state s) (inputs i) = Zmod.unsigned (N.v47158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47158 s i)) at 1.
  unfold R.v47158, N.v47158.
  rewrite ?node_47153.
  rewrite ?node_47157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47159 (s : N.State) (i : N.Inputs) :
  R.v47159 (state s) (inputs i) = Zmod.unsigned (N.v47159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47159 s i)) at 1.
  unfold R.v47159, N.v47159.
  unfold R.v6, N.v6.
  rewrite ?node_47158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47160 (s : N.State) (i : N.Inputs) :
  R.v47160 (state s) (inputs i) = Zmod.unsigned (N.v47160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47160 s i)) at 1.
  unfold R.v47160, N.v47160.
  rewrite ?node_14683.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47161 (s : N.State) (i : N.Inputs) :
  R.v47161 (state s) (inputs i) = Zmod.unsigned (N.v47161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47161 s i)) at 1.
  unfold R.v47161, N.v47161.
  unfold R.v6, N.v6.
  rewrite ?node_14779.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47162 (s : N.State) (i : N.Inputs) :
  R.v47162 (state s) (inputs i) = Zmod.unsigned (N.v47162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47162 s i)) at 1.
  unfold R.v47162, N.v47162.
  rewrite ?node_47160.
  rewrite ?node_47161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47163 (s : N.State) (i : N.Inputs) :
  R.v47163 (state s) (inputs i) = Zmod.unsigned (N.v47163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47163 s i)) at 1.
  unfold R.v47163, N.v47163.
  rewrite ?node_47159.
  rewrite ?node_47162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47164 (s : N.State) (i : N.Inputs) :
  R.v47164 (state s) (inputs i) = Zmod.unsigned (N.v47164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47164 s i)) at 1.
  unfold R.v47164, N.v47164.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47165 (s : N.State) (i : N.Inputs) :
  R.v47165 (state s) (inputs i) = Zmod.unsigned (N.v47165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47165 s i)) at 1.
  unfold R.v47165, N.v47165.
  rewrite ?node_14690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47166 (s : N.State) (i : N.Inputs) :
  R.v47166 (state s) (inputs i) = Zmod.unsigned (N.v47166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47166 s i)) at 1.
  unfold R.v47166, N.v47166.
  unfold R.v6, N.v6.
  rewrite ?node_14686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47167 (s : N.State) (i : N.Inputs) :
  R.v47167 (state s) (inputs i) = Zmod.unsigned (N.v47167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47167 s i)) at 1.
  unfold R.v47167, N.v47167.
  unfold R.v6, N.v6.
  rewrite ?node_14683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47168 (s : N.State) (i : N.Inputs) :
  R.v47168 (state s) (inputs i) = Zmod.unsigned (N.v47168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47168 s i)) at 1.
  unfold R.v47168, N.v47168.
  rewrite ?node_47166.
  rewrite ?node_47167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47169 (s : N.State) (i : N.Inputs) :
  R.v47169 (state s) (inputs i) = Zmod.unsigned (N.v47169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47169 s i)) at 1.
  unfold R.v47169, N.v47169.
  unfold R.v16484, N.v16484.
  rewrite ?node_47168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47170 (s : N.State) (i : N.Inputs) :
  R.v47170 (state s) (inputs i) = Zmod.unsigned (N.v47170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47170 s i)) at 1.
  unfold R.v47170, N.v47170.
  rewrite ?node_47165.
  rewrite ?node_47169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47171 (s : N.State) (i : N.Inputs) :
  R.v47171 (state s) (inputs i) = Zmod.unsigned (N.v47171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47171 s i)) at 1.
  unfold R.v47171, N.v47171.
  unfold R.v6, N.v6.
  rewrite ?node_47170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47172 (s : N.State) (i : N.Inputs) :
  R.v47172 (state s) (inputs i) = Zmod.unsigned (N.v47172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47172 s i)) at 1.
  unfold R.v47172, N.v47172.
  rewrite ?node_14691.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47173 (s : N.State) (i : N.Inputs) :
  R.v47173 (state s) (inputs i) = Zmod.unsigned (N.v47173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47173 s i)) at 1.
  unfold R.v47173, N.v47173.
  unfold R.v6, N.v6.
  rewrite ?node_14796.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47174 (s : N.State) (i : N.Inputs) :
  R.v47174 (state s) (inputs i) = Zmod.unsigned (N.v47174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47174 s i)) at 1.
  unfold R.v47174, N.v47174.
  rewrite ?node_47172.
  rewrite ?node_47173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47175 (s : N.State) (i : N.Inputs) :
  R.v47175 (state s) (inputs i) = Zmod.unsigned (N.v47175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47175 s i)) at 1.
  unfold R.v47175, N.v47175.
  rewrite ?node_47171.
  rewrite ?node_47174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47176 (s : N.State) (i : N.Inputs) :
  R.v47176 (state s) (inputs i) = Zmod.unsigned (N.v47176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47176 s i)) at 1.
  unfold R.v47176, N.v47176.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47177 (s : N.State) (i : N.Inputs) :
  R.v47177 (state s) (inputs i) = Zmod.unsigned (N.v47177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47177 s i)) at 1.
  unfold R.v47177, N.v47177.
  unfold R.v6, N.v6.
  rewrite ?node_14696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47178 (s : N.State) (i : N.Inputs) :
  R.v47178 (state s) (inputs i) = Zmod.unsigned (N.v47178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47178 s i)) at 1.
  unfold R.v47178, N.v47178.
  unfold R.v6, N.v6.
  rewrite ?node_14695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47179 (s : N.State) (i : N.Inputs) :
  R.v47179 (state s) (inputs i) = Zmod.unsigned (N.v47179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47179 s i)) at 1.
  unfold R.v47179, N.v47179.
  rewrite ?node_47177.
  rewrite ?node_47178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47180 (s : N.State) (i : N.Inputs) :
  R.v47180 (state s) (inputs i) = Zmod.unsigned (N.v47180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47180 s i)) at 1.
  unfold R.v47180, N.v47180.
  unfold R.v16463, N.v16463.
  rewrite ?node_47179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47181 (s : N.State) (i : N.Inputs) :
  R.v47181 (state s) (inputs i) = Zmod.unsigned (N.v47181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47181 s i)) at 1.
  unfold R.v47181, N.v47181.
  rewrite ?node_14697.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47182 (s : N.State) (i : N.Inputs) :
  R.v47182 (state s) (inputs i) = Zmod.unsigned (N.v47182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47182 s i)) at 1.
  unfold R.v47182, N.v47182.
  unfold R.v6, N.v6.
  rewrite ?node_14797.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47183 (s : N.State) (i : N.Inputs) :
  R.v47183 (state s) (inputs i) = Zmod.unsigned (N.v47183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47183 s i)) at 1.
  unfold R.v47183, N.v47183.
  rewrite ?node_47181.
  rewrite ?node_47182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47184 (s : N.State) (i : N.Inputs) :
  R.v47184 (state s) (inputs i) = Zmod.unsigned (N.v47184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47184 s i)) at 1.
  unfold R.v47184, N.v47184.
  rewrite ?node_47180.
  rewrite ?node_47183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47185 (s : N.State) (i : N.Inputs) :
  R.v47185 (state s) (inputs i) = Zmod.unsigned (N.v47185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47185 s i)) at 1.
  unfold R.v47185, N.v47185.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47186 (s : N.State) (i : N.Inputs) :
  R.v47186 (state s) (inputs i) = Zmod.unsigned (N.v47186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47186 s i)) at 1.
  unfold R.v47186, N.v47186.
  rewrite ?node_14763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47187 (s : N.State) (i : N.Inputs) :
  R.v47187 (state s) (inputs i) = Zmod.unsigned (N.v47187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47187 s i)) at 1.
  unfold R.v47187, N.v47187.
  rewrite ?node_14759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47188 (s : N.State) (i : N.Inputs) :
  R.v47188 (state s) (inputs i) = Zmod.unsigned (N.v47188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47188 s i)) at 1.
  unfold R.v47188, N.v47188.
  rewrite ?node_14751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47189 (s : N.State) (i : N.Inputs) :
  R.v47189 (state s) (inputs i) = Zmod.unsigned (N.v47189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47189 s i)) at 1.
  unfold R.v47189, N.v47189.
  unfold R.v6, N.v6.
  rewrite ?node_14743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47190 (s : N.State) (i : N.Inputs) :
  R.v47190 (state s) (inputs i) = Zmod.unsigned (N.v47190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47190 s i)) at 1.
  unfold R.v47190, N.v47190.
  unfold R.v6, N.v6.
  rewrite ?node_14736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47191 (s : N.State) (i : N.Inputs) :
  R.v47191 (state s) (inputs i) = Zmod.unsigned (N.v47191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47191 s i)) at 1.
  unfold R.v47191, N.v47191.
  rewrite ?node_47189.
  rewrite ?node_47190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47192 (s : N.State) (i : N.Inputs) :
  R.v47192 (state s) (inputs i) = Zmod.unsigned (N.v47192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47192 s i)) at 1.
  unfold R.v47192, N.v47192.
  unfold R.v16484, N.v16484.
  rewrite ?node_47191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47193 (s : N.State) (i : N.Inputs) :
  R.v47193 (state s) (inputs i) = Zmod.unsigned (N.v47193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47193 s i)) at 1.
  unfold R.v47193, N.v47193.
  rewrite ?node_47186.
  rewrite ?node_47187.
  rewrite ?node_47188.
  rewrite ?node_47192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47194 (s : N.State) (i : N.Inputs) :
  R.v47194 (state s) (inputs i) = Zmod.unsigned (N.v47194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47194 s i)) at 1.
  unfold R.v47194, N.v47194.
  unfold R.v6, N.v6.
  rewrite ?node_47193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47195 (s : N.State) (i : N.Inputs) :
  R.v47195 (state s) (inputs i) = Zmod.unsigned (N.v47195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47195 s i)) at 1.
  unfold R.v47195, N.v47195.
  rewrite ?node_14764.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47196 (s : N.State) (i : N.Inputs) :
  R.v47196 (state s) (inputs i) = Zmod.unsigned (N.v47196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47196 s i)) at 1.
  unfold R.v47196, N.v47196.
  unfold R.v6, N.v6.
  rewrite ?node_14849.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47197 (s : N.State) (i : N.Inputs) :
  R.v47197 (state s) (inputs i) = Zmod.unsigned (N.v47197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47197 s i)) at 1.
  unfold R.v47197, N.v47197.
  unfold R.v6, N.v6.
  rewrite ?node_14873.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47198 (s : N.State) (i : N.Inputs) :
  R.v47198 (state s) (inputs i) = Zmod.unsigned (N.v47198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47198 s i)) at 1.
  unfold R.v47198, N.v47198.
  rewrite ?node_47195.
  rewrite ?node_47196.
  rewrite ?node_47197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47199 (s : N.State) (i : N.Inputs) :
  R.v47199 (state s) (inputs i) = Zmod.unsigned (N.v47199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47199 s i)) at 1.
  unfold R.v47199, N.v47199.
  rewrite ?node_47194.
  rewrite ?node_47198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47200 (s : N.State) (i : N.Inputs) :
  R.v47200 (state s) (inputs i) = Zmod.unsigned (N.v47200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47200 s i)) at 1.
  unfold R.v47200, N.v47200.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47201 (s : N.State) (i : N.Inputs) :
  R.v47201 (state s) (inputs i) = Zmod.unsigned (N.v47201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47201 s i)) at 1.
  unfold R.v47201, N.v47201.
  rewrite ?node_14751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47202 (s : N.State) (i : N.Inputs) :
  R.v47202 (state s) (inputs i) = Zmod.unsigned (N.v47202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47202 s i)) at 1.
  unfold R.v47202, N.v47202.
  unfold R.v6, N.v6.
  rewrite ?node_14743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47203 (s : N.State) (i : N.Inputs) :
  R.v47203 (state s) (inputs i) = Zmod.unsigned (N.v47203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47203 s i)) at 1.
  unfold R.v47203, N.v47203.
  unfold R.v6, N.v6.
  rewrite ?node_14736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47204 (s : N.State) (i : N.Inputs) :
  R.v47204 (state s) (inputs i) = Zmod.unsigned (N.v47204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47204 s i)) at 1.
  unfold R.v47204, N.v47204.
  rewrite ?node_47202.
  rewrite ?node_47203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47205 (s : N.State) (i : N.Inputs) :
  R.v47205 (state s) (inputs i) = Zmod.unsigned (N.v47205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47205 s i)) at 1.
  unfold R.v47205, N.v47205.
  unfold R.v16484, N.v16484.
  rewrite ?node_47204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47206 (s : N.State) (i : N.Inputs) :
  R.v47206 (state s) (inputs i) = Zmod.unsigned (N.v47206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47206 s i)) at 1.
  unfold R.v47206, N.v47206.
  rewrite ?node_47201.
  rewrite ?node_47205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47207 (s : N.State) (i : N.Inputs) :
  R.v47207 (state s) (inputs i) = Zmod.unsigned (N.v47207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47207 s i)) at 1.
  unfold R.v47207, N.v47207.
  unfold R.v6, N.v6.
  rewrite ?node_47206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47208 (s : N.State) (i : N.Inputs) :
  R.v47208 (state s) (inputs i) = Zmod.unsigned (N.v47208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47208 s i)) at 1.
  unfold R.v47208, N.v47208.
  rewrite ?node_14752.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47209 (s : N.State) (i : N.Inputs) :
  R.v47209 (state s) (inputs i) = Zmod.unsigned (N.v47209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47209 s i)) at 1.
  unfold R.v47209, N.v47209.
  unfold R.v6, N.v6.
  rewrite ?node_14849.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47210 (s : N.State) (i : N.Inputs) :
  R.v47210 (state s) (inputs i) = Zmod.unsigned (N.v47210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47210 s i)) at 1.
  unfold R.v47210, N.v47210.
  rewrite ?node_47208.
  rewrite ?node_47209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47211 (s : N.State) (i : N.Inputs) :
  R.v47211 (state s) (inputs i) = Zmod.unsigned (N.v47211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47211 s i)) at 1.
  unfold R.v47211, N.v47211.
  rewrite ?node_47207.
  rewrite ?node_47210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47212 (s : N.State) (i : N.Inputs) :
  R.v47212 (state s) (inputs i) = Zmod.unsigned (N.v47212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47212 s i)) at 1.
  unfold R.v47212, N.v47212.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47213 (s : N.State) (i : N.Inputs) :
  R.v47213 (state s) (inputs i) = Zmod.unsigned (N.v47213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47213 s i)) at 1.
  unfold R.v47213, N.v47213.
  rewrite ?node_14763.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47214 (s : N.State) (i : N.Inputs) :
  R.v47214 (state s) (inputs i) = Zmod.unsigned (N.v47214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47214 s i)) at 1.
  unfold R.v47214, N.v47214.
  unfold R.v6, N.v6.
  rewrite ?node_14759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47215 (s : N.State) (i : N.Inputs) :
  R.v47215 (state s) (inputs i) = Zmod.unsigned (N.v47215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47215 s i)) at 1.
  unfold R.v47215, N.v47215.
  unfold R.v6, N.v6.
  rewrite ?node_14752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47216 (s : N.State) (i : N.Inputs) :
  R.v47216 (state s) (inputs i) = Zmod.unsigned (N.v47216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47216 s i)) at 1.
  unfold R.v47216, N.v47216.
  rewrite ?node_47214.
  rewrite ?node_47215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47217 (s : N.State) (i : N.Inputs) :
  R.v47217 (state s) (inputs i) = Zmod.unsigned (N.v47217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47217 s i)) at 1.
  unfold R.v47217, N.v47217.
  unfold R.v16484, N.v16484.
  rewrite ?node_47216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47218 (s : N.State) (i : N.Inputs) :
  R.v47218 (state s) (inputs i) = Zmod.unsigned (N.v47218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47218 s i)) at 1.
  unfold R.v47218, N.v47218.
  rewrite ?node_47213.
  rewrite ?node_47217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47219 (s : N.State) (i : N.Inputs) :
  R.v47219 (state s) (inputs i) = Zmod.unsigned (N.v47219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47219 s i)) at 1.
  unfold R.v47219, N.v47219.
  unfold R.v6, N.v6.
  rewrite ?node_47218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47220 (s : N.State) (i : N.Inputs) :
  R.v47220 (state s) (inputs i) = Zmod.unsigned (N.v47220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47220 s i)) at 1.
  unfold R.v47220, N.v47220.
  rewrite ?node_14764.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47221 (s : N.State) (i : N.Inputs) :
  R.v47221 (state s) (inputs i) = Zmod.unsigned (N.v47221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47221 s i)) at 1.
  unfold R.v47221, N.v47221.
  unfold R.v6, N.v6.
  rewrite ?node_14873.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47222 (s : N.State) (i : N.Inputs) :
  R.v47222 (state s) (inputs i) = Zmod.unsigned (N.v47222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47222 s i)) at 1.
  unfold R.v47222, N.v47222.
  rewrite ?node_47220.
  rewrite ?node_47221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47223 (s : N.State) (i : N.Inputs) :
  R.v47223 (state s) (inputs i) = Zmod.unsigned (N.v47223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47223 s i)) at 1.
  unfold R.v47223, N.v47223.
  rewrite ?node_47219.
  rewrite ?node_47222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47224 (s : N.State) (i : N.Inputs) :
  R.v47224 (state s) (inputs i) = Zmod.unsigned (N.v47224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47224 s i)) at 1.
  unfold R.v47224, N.v47224.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47225 (s : N.State) (i : N.Inputs) :
  R.v47225 (state s) (inputs i) = Zmod.unsigned (N.v47225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47225 s i)) at 1.
  unfold R.v47225, N.v47225.
  rewrite ?node_14779.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47226 (s : N.State) (i : N.Inputs) :
  R.v47226 (state s) (inputs i) = Zmod.unsigned (N.v47226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47226 s i)) at 1.
  unfold R.v47226, N.v47226.
  rewrite ?node_14775.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47227 (s : N.State) (i : N.Inputs) :
  R.v47227 (state s) (inputs i) = Zmod.unsigned (N.v47227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47227 s i)) at 1.
  unfold R.v47227, N.v47227.
  rewrite ?node_14771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47228 (s : N.State) (i : N.Inputs) :
  R.v47228 (state s) (inputs i) = Zmod.unsigned (N.v47228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47228 s i)) at 1.
  unfold R.v47228, N.v47228.
  unfold R.v6, N.v6.
  rewrite ?node_14767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47229 (s : N.State) (i : N.Inputs) :
  R.v47229 (state s) (inputs i) = Zmod.unsigned (N.v47229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47229 s i)) at 1.
  unfold R.v47229, N.v47229.
  unfold R.v6, N.v6.
  rewrite !state_r2022_nr_5F2038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2022_nr_5F2038 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47230 (s : N.State) (i : N.Inputs) :
  R.v47230 (state s) (inputs i) = Zmod.unsigned (N.v47230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47230 s i)) at 1.
  unfold R.v47230, N.v47230.
  rewrite ?node_47228.
  rewrite ?node_47229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47231 (s : N.State) (i : N.Inputs) :
  R.v47231 (state s) (inputs i) = Zmod.unsigned (N.v47231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47231 s i)) at 1.
  unfold R.v47231, N.v47231.
  unfold R.v16484, N.v16484.
  rewrite ?node_47230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47232 (s : N.State) (i : N.Inputs) :
  R.v47232 (state s) (inputs i) = Zmod.unsigned (N.v47232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47232 s i)) at 1.
  unfold R.v47232, N.v47232.
  rewrite ?node_47225.
  rewrite ?node_47226.
  rewrite ?node_47227.
  rewrite ?node_47231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47233 (s : N.State) (i : N.Inputs) :
  R.v47233 (state s) (inputs i) = Zmod.unsigned (N.v47233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47233 s i)) at 1.
  unfold R.v47233, N.v47233.
  unfold R.v6, N.v6.
  rewrite ?node_47232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47234 (s : N.State) (i : N.Inputs) :
  R.v47234 (state s) (inputs i) = Zmod.unsigned (N.v47234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47234 s i)) at 1.
  unfold R.v47234, N.v47234.
  rewrite ?node_14780.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47235 (s : N.State) (i : N.Inputs) :
  R.v47235 (state s) (inputs i) = Zmod.unsigned (N.v47235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47235 s i)) at 1.
  unfold R.v47235, N.v47235.
  unfold R.v6, N.v6.
  rewrite ?node_14868.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47236 (s : N.State) (i : N.Inputs) :
  R.v47236 (state s) (inputs i) = Zmod.unsigned (N.v47236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47236 s i)) at 1.
  unfold R.v47236, N.v47236.
  unfold R.v6, N.v6.
  rewrite ?node_14877.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47237 (s : N.State) (i : N.Inputs) :
  R.v47237 (state s) (inputs i) = Zmod.unsigned (N.v47237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47237 s i)) at 1.
  unfold R.v47237, N.v47237.
  rewrite ?node_47234.
  rewrite ?node_47235.
  rewrite ?node_47236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47238 (s : N.State) (i : N.Inputs) :
  R.v47238 (state s) (inputs i) = Zmod.unsigned (N.v47238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47238 s i)) at 1.
  unfold R.v47238, N.v47238.
  rewrite ?node_47233.
  rewrite ?node_47237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47239 (s : N.State) (i : N.Inputs) :
  R.v47239 (state s) (inputs i) = Zmod.unsigned (N.v47239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47239 s i)) at 1.
  unfold R.v47239, N.v47239.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47240 (s : N.State) (i : N.Inputs) :
  R.v47240 (state s) (inputs i) = Zmod.unsigned (N.v47240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47240 s i)) at 1.
  unfold R.v47240, N.v47240.
  rewrite ?node_14771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47241 (s : N.State) (i : N.Inputs) :
  R.v47241 (state s) (inputs i) = Zmod.unsigned (N.v47241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47241 s i)) at 1.
  unfold R.v47241, N.v47241.
  unfold R.v6, N.v6.
  rewrite ?node_14767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47242 (s : N.State) (i : N.Inputs) :
  R.v47242 (state s) (inputs i) = Zmod.unsigned (N.v47242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47242 s i)) at 1.
  unfold R.v47242, N.v47242.
  unfold R.v6, N.v6.
  rewrite !state_r2022_nr_5F2038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2022_nr_5F2038 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47243 (s : N.State) (i : N.Inputs) :
  R.v47243 (state s) (inputs i) = Zmod.unsigned (N.v47243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47243 s i)) at 1.
  unfold R.v47243, N.v47243.
  rewrite ?node_47241.
  rewrite ?node_47242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47244 (s : N.State) (i : N.Inputs) :
  R.v47244 (state s) (inputs i) = Zmod.unsigned (N.v47244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47244 s i)) at 1.
  unfold R.v47244, N.v47244.
  unfold R.v16484, N.v16484.
  rewrite ?node_47243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47245 (s : N.State) (i : N.Inputs) :
  R.v47245 (state s) (inputs i) = Zmod.unsigned (N.v47245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47245 s i)) at 1.
  unfold R.v47245, N.v47245.
  rewrite ?node_47240.
  rewrite ?node_47244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47246 (s : N.State) (i : N.Inputs) :
  R.v47246 (state s) (inputs i) = Zmod.unsigned (N.v47246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47246 s i)) at 1.
  unfold R.v47246, N.v47246.
  unfold R.v6, N.v6.
  rewrite ?node_47245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47247 (s : N.State) (i : N.Inputs) :
  R.v47247 (state s) (inputs i) = Zmod.unsigned (N.v47247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47247 s i)) at 1.
  unfold R.v47247, N.v47247.
  rewrite ?node_14772.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47248 (s : N.State) (i : N.Inputs) :
  R.v47248 (state s) (inputs i) = Zmod.unsigned (N.v47248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47248 s i)) at 1.
  unfold R.v47248, N.v47248.
  unfold R.v6, N.v6.
  rewrite ?node_14868.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47249 (s : N.State) (i : N.Inputs) :
  R.v47249 (state s) (inputs i) = Zmod.unsigned (N.v47249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47249 s i)) at 1.
  unfold R.v47249, N.v47249.
  rewrite ?node_47247.
  rewrite ?node_47248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47250 (s : N.State) (i : N.Inputs) :
  R.v47250 (state s) (inputs i) = Zmod.unsigned (N.v47250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47250 s i)) at 1.
  unfold R.v47250, N.v47250.
  rewrite ?node_47246.
  rewrite ?node_47249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47251 (s : N.State) (i : N.Inputs) :
  R.v47251 (state s) (inputs i) = Zmod.unsigned (N.v47251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47251 s i)) at 1.
  unfold R.v47251, N.v47251.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47252 (s : N.State) (i : N.Inputs) :
  R.v47252 (state s) (inputs i) = Zmod.unsigned (N.v47252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47252 s i)) at 1.
  unfold R.v47252, N.v47252.
  rewrite ?node_14779.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47253 (s : N.State) (i : N.Inputs) :
  R.v47253 (state s) (inputs i) = Zmod.unsigned (N.v47253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47253 s i)) at 1.
  unfold R.v47253, N.v47253.
  unfold R.v6, N.v6.
  rewrite ?node_14775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47254 (s : N.State) (i : N.Inputs) :
  R.v47254 (state s) (inputs i) = Zmod.unsigned (N.v47254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47254 s i)) at 1.
  unfold R.v47254, N.v47254.
  unfold R.v6, N.v6.
  rewrite ?node_14772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47255 (s : N.State) (i : N.Inputs) :
  R.v47255 (state s) (inputs i) = Zmod.unsigned (N.v47255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47255 s i)) at 1.
  unfold R.v47255, N.v47255.
  rewrite ?node_47253.
  rewrite ?node_47254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47256 (s : N.State) (i : N.Inputs) :
  R.v47256 (state s) (inputs i) = Zmod.unsigned (N.v47256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47256 s i)) at 1.
  unfold R.v47256, N.v47256.
  unfold R.v16484, N.v16484.
  rewrite ?node_47255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47257 (s : N.State) (i : N.Inputs) :
  R.v47257 (state s) (inputs i) = Zmod.unsigned (N.v47257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47257 s i)) at 1.
  unfold R.v47257, N.v47257.
  rewrite ?node_47252.
  rewrite ?node_47256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47258 (s : N.State) (i : N.Inputs) :
  R.v47258 (state s) (inputs i) = Zmod.unsigned (N.v47258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47258 s i)) at 1.
  unfold R.v47258, N.v47258.
  unfold R.v6, N.v6.
  rewrite ?node_47257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47259 (s : N.State) (i : N.Inputs) :
  R.v47259 (state s) (inputs i) = Zmod.unsigned (N.v47259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47259 s i)) at 1.
  unfold R.v47259, N.v47259.
  rewrite ?node_14780.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47260 (s : N.State) (i : N.Inputs) :
  R.v47260 (state s) (inputs i) = Zmod.unsigned (N.v47260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47260 s i)) at 1.
  unfold R.v47260, N.v47260.
  unfold R.v6, N.v6.
  rewrite ?node_14877.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47261 (s : N.State) (i : N.Inputs) :
  R.v47261 (state s) (inputs i) = Zmod.unsigned (N.v47261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47261 s i)) at 1.
  unfold R.v47261, N.v47261.
  rewrite ?node_47259.
  rewrite ?node_47260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47262 (s : N.State) (i : N.Inputs) :
  R.v47262 (state s) (inputs i) = Zmod.unsigned (N.v47262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47262 s i)) at 1.
  unfold R.v47262, N.v47262.
  rewrite ?node_47258.
  rewrite ?node_47261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47263 (s : N.State) (i : N.Inputs) :
  R.v47263 (state s) (inputs i) = Zmod.unsigned (N.v47263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47263 s i)) at 1.
  unfold R.v47263, N.v47263.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47264 (s : N.State) (i : N.Inputs) :
  R.v47264 (state s) (inputs i) = Zmod.unsigned (N.v47264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47264 s i)) at 1.
  unfold R.v47264, N.v47264.
  rewrite ?node_14849.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47265 (s : N.State) (i : N.Inputs) :
  R.v47265 (state s) (inputs i) = Zmod.unsigned (N.v47265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47265 s i)) at 1.
  unfold R.v47265, N.v47265.
  rewrite ?node_14845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47266 (s : N.State) (i : N.Inputs) :
  R.v47266 (state s) (inputs i) = Zmod.unsigned (N.v47266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47266 s i)) at 1.
  unfold R.v47266, N.v47266.
  rewrite ?node_14837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47267 (s : N.State) (i : N.Inputs) :
  R.v47267 (state s) (inputs i) = Zmod.unsigned (N.v47267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47267 s i)) at 1.
  unfold R.v47267, N.v47267.
  unfold R.v6, N.v6.
  rewrite ?node_14829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47268 (s : N.State) (i : N.Inputs) :
  R.v47268 (state s) (inputs i) = Zmod.unsigned (N.v47268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47268 s i)) at 1.
  unfold R.v47268, N.v47268.
  unfold R.v6, N.v6.
  rewrite ?node_14822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47269 (s : N.State) (i : N.Inputs) :
  R.v47269 (state s) (inputs i) = Zmod.unsigned (N.v47269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47269 s i)) at 1.
  unfold R.v47269, N.v47269.
  rewrite ?node_47267.
  rewrite ?node_47268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47270 (s : N.State) (i : N.Inputs) :
  R.v47270 (state s) (inputs i) = Zmod.unsigned (N.v47270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47270 s i)) at 1.
  unfold R.v47270, N.v47270.
  unfold R.v16484, N.v16484.
  rewrite ?node_47269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47271 (s : N.State) (i : N.Inputs) :
  R.v47271 (state s) (inputs i) = Zmod.unsigned (N.v47271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47271 s i)) at 1.
  unfold R.v47271, N.v47271.
  rewrite ?node_47264.
  rewrite ?node_47265.
  rewrite ?node_47266.
  rewrite ?node_47270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47272 (s : N.State) (i : N.Inputs) :
  R.v47272 (state s) (inputs i) = Zmod.unsigned (N.v47272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47272 s i)) at 1.
  unfold R.v47272, N.v47272.
  unfold R.v6, N.v6.
  rewrite ?node_47271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47273 (s : N.State) (i : N.Inputs) :
  R.v47273 (state s) (inputs i) = Zmod.unsigned (N.v47273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47273 s i)) at 1.
  unfold R.v47273, N.v47273.
  rewrite ?node_14850.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47274 (s : N.State) (i : N.Inputs) :
  R.v47274 (state s) (inputs i) = Zmod.unsigned (N.v47274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47274 s i)) at 1.
  unfold R.v47274, N.v47274.
  unfold R.v6, N.v6.
  rewrite ?node_14933.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47275 (s : N.State) (i : N.Inputs) :
  R.v47275 (state s) (inputs i) = Zmod.unsigned (N.v47275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47275 s i)) at 1.
  unfold R.v47275, N.v47275.
  unfold R.v6, N.v6.
  rewrite ?node_14957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47276 (s : N.State) (i : N.Inputs) :
  R.v47276 (state s) (inputs i) = Zmod.unsigned (N.v47276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47276 s i)) at 1.
  unfold R.v47276, N.v47276.
  rewrite ?node_47273.
  rewrite ?node_47274.
  rewrite ?node_47275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47277 (s : N.State) (i : N.Inputs) :
  R.v47277 (state s) (inputs i) = Zmod.unsigned (N.v47277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47277 s i)) at 1.
  unfold R.v47277, N.v47277.
  rewrite ?node_47272.
  rewrite ?node_47276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47278 (s : N.State) (i : N.Inputs) :
  R.v47278 (state s) (inputs i) = Zmod.unsigned (N.v47278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47278 s i)) at 1.
  unfold R.v47278, N.v47278.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47279 (s : N.State) (i : N.Inputs) :
  R.v47279 (state s) (inputs i) = Zmod.unsigned (N.v47279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47279 s i)) at 1.
  unfold R.v47279, N.v47279.
  rewrite ?node_14837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47280 (s : N.State) (i : N.Inputs) :
  R.v47280 (state s) (inputs i) = Zmod.unsigned (N.v47280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47280 s i)) at 1.
  unfold R.v47280, N.v47280.
  unfold R.v6, N.v6.
  rewrite ?node_14829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47281 (s : N.State) (i : N.Inputs) :
  R.v47281 (state s) (inputs i) = Zmod.unsigned (N.v47281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47281 s i)) at 1.
  unfold R.v47281, N.v47281.
  unfold R.v6, N.v6.
  rewrite ?node_14822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47282 (s : N.State) (i : N.Inputs) :
  R.v47282 (state s) (inputs i) = Zmod.unsigned (N.v47282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47282 s i)) at 1.
  unfold R.v47282, N.v47282.
  rewrite ?node_47280.
  rewrite ?node_47281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47283 (s : N.State) (i : N.Inputs) :
  R.v47283 (state s) (inputs i) = Zmod.unsigned (N.v47283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47283 s i)) at 1.
  unfold R.v47283, N.v47283.
  unfold R.v16484, N.v16484.
  rewrite ?node_47282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47284 (s : N.State) (i : N.Inputs) :
  R.v47284 (state s) (inputs i) = Zmod.unsigned (N.v47284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47284 s i)) at 1.
  unfold R.v47284, N.v47284.
  rewrite ?node_47279.
  rewrite ?node_47283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47285 (s : N.State) (i : N.Inputs) :
  R.v47285 (state s) (inputs i) = Zmod.unsigned (N.v47285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47285 s i)) at 1.
  unfold R.v47285, N.v47285.
  unfold R.v6, N.v6.
  rewrite ?node_47284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47286 (s : N.State) (i : N.Inputs) :
  R.v47286 (state s) (inputs i) = Zmod.unsigned (N.v47286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47286 s i)) at 1.
  unfold R.v47286, N.v47286.
  rewrite ?node_14838.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47287 (s : N.State) (i : N.Inputs) :
  R.v47287 (state s) (inputs i) = Zmod.unsigned (N.v47287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47287 s i)) at 1.
  unfold R.v47287, N.v47287.
  unfold R.v6, N.v6.
  rewrite ?node_14933.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47288 (s : N.State) (i : N.Inputs) :
  R.v47288 (state s) (inputs i) = Zmod.unsigned (N.v47288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47288 s i)) at 1.
  unfold R.v47288, N.v47288.
  rewrite ?node_47286.
  rewrite ?node_47287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47289 (s : N.State) (i : N.Inputs) :
  R.v47289 (state s) (inputs i) = Zmod.unsigned (N.v47289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47289 s i)) at 1.
  unfold R.v47289, N.v47289.
  rewrite ?node_47285.
  rewrite ?node_47288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47290 (s : N.State) (i : N.Inputs) :
  R.v47290 (state s) (inputs i) = Zmod.unsigned (N.v47290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47290 s i)) at 1.
  unfold R.v47290, N.v47290.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47291 (s : N.State) (i : N.Inputs) :
  R.v47291 (state s) (inputs i) = Zmod.unsigned (N.v47291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47291 s i)) at 1.
  unfold R.v47291, N.v47291.
  rewrite ?node_14849.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47292 (s : N.State) (i : N.Inputs) :
  R.v47292 (state s) (inputs i) = Zmod.unsigned (N.v47292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47292 s i)) at 1.
  unfold R.v47292, N.v47292.
  unfold R.v6, N.v6.
  rewrite ?node_14845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47293 (s : N.State) (i : N.Inputs) :
  R.v47293 (state s) (inputs i) = Zmod.unsigned (N.v47293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47293 s i)) at 1.
  unfold R.v47293, N.v47293.
  unfold R.v6, N.v6.
  rewrite ?node_14838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47294 (s : N.State) (i : N.Inputs) :
  R.v47294 (state s) (inputs i) = Zmod.unsigned (N.v47294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47294 s i)) at 1.
  unfold R.v47294, N.v47294.
  rewrite ?node_47292.
  rewrite ?node_47293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47295 (s : N.State) (i : N.Inputs) :
  R.v47295 (state s) (inputs i) = Zmod.unsigned (N.v47295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47295 s i)) at 1.
  unfold R.v47295, N.v47295.
  unfold R.v16484, N.v16484.
  rewrite ?node_47294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47296 (s : N.State) (i : N.Inputs) :
  R.v47296 (state s) (inputs i) = Zmod.unsigned (N.v47296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47296 s i)) at 1.
  unfold R.v47296, N.v47296.
  rewrite ?node_47291.
  rewrite ?node_47295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47297 (s : N.State) (i : N.Inputs) :
  R.v47297 (state s) (inputs i) = Zmod.unsigned (N.v47297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47297 s i)) at 1.
  unfold R.v47297, N.v47297.
  unfold R.v6, N.v6.
  rewrite ?node_47296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47298 (s : N.State) (i : N.Inputs) :
  R.v47298 (state s) (inputs i) = Zmod.unsigned (N.v47298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47298 s i)) at 1.
  unfold R.v47298, N.v47298.
  rewrite ?node_14850.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47299 (s : N.State) (i : N.Inputs) :
  R.v47299 (state s) (inputs i) = Zmod.unsigned (N.v47299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47299 s i)) at 1.
  unfold R.v47299, N.v47299.
  unfold R.v6, N.v6.
  rewrite ?node_14957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47300 (s : N.State) (i : N.Inputs) :
  R.v47300 (state s) (inputs i) = Zmod.unsigned (N.v47300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47300 s i)) at 1.
  unfold R.v47300, N.v47300.
  rewrite ?node_47298.
  rewrite ?node_47299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47301 (s : N.State) (i : N.Inputs) :
  R.v47301 (state s) (inputs i) = Zmod.unsigned (N.v47301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47301 s i)) at 1.
  unfold R.v47301, N.v47301.
  rewrite ?node_47297.
  rewrite ?node_47300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47302 (s : N.State) (i : N.Inputs) :
  R.v47302 (state s) (inputs i) = Zmod.unsigned (N.v47302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47302 s i)) at 1.
  unfold R.v47302, N.v47302.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47303 (s : N.State) (i : N.Inputs) :
  R.v47303 (state s) (inputs i) = Zmod.unsigned (N.v47303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47303 s i)) at 1.
  unfold R.v47303, N.v47303.
  rewrite ?node_14868.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47304 (s : N.State) (i : N.Inputs) :
  R.v47304 (state s) (inputs i) = Zmod.unsigned (N.v47304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47304 s i)) at 1.
  unfold R.v47304, N.v47304.
  rewrite ?node_14864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47305 (s : N.State) (i : N.Inputs) :
  R.v47305 (state s) (inputs i) = Zmod.unsigned (N.v47305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47305 s i)) at 1.
  unfold R.v47305, N.v47305.
  rewrite ?node_14860.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47306 (s : N.State) (i : N.Inputs) :
  R.v47306 (state s) (inputs i) = Zmod.unsigned (N.v47306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47306 s i)) at 1.
  unfold R.v47306, N.v47306.
  unfold R.v6, N.v6.
  rewrite ?node_14856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47307 (s : N.State) (i : N.Inputs) :
  R.v47307 (state s) (inputs i) = Zmod.unsigned (N.v47307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47307 s i)) at 1.
  unfold R.v47307, N.v47307.
  unfold R.v6, N.v6.
  rewrite ?node_14853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47308 (s : N.State) (i : N.Inputs) :
  R.v47308 (state s) (inputs i) = Zmod.unsigned (N.v47308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47308 s i)) at 1.
  unfold R.v47308, N.v47308.
  rewrite ?node_47306.
  rewrite ?node_47307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47309 (s : N.State) (i : N.Inputs) :
  R.v47309 (state s) (inputs i) = Zmod.unsigned (N.v47309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47309 s i)) at 1.
  unfold R.v47309, N.v47309.
  unfold R.v16484, N.v16484.
  rewrite ?node_47308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47310 (s : N.State) (i : N.Inputs) :
  R.v47310 (state s) (inputs i) = Zmod.unsigned (N.v47310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47310 s i)) at 1.
  unfold R.v47310, N.v47310.
  rewrite ?node_47303.
  rewrite ?node_47304.
  rewrite ?node_47305.
  rewrite ?node_47309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47311 (s : N.State) (i : N.Inputs) :
  R.v47311 (state s) (inputs i) = Zmod.unsigned (N.v47311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47311 s i)) at 1.
  unfold R.v47311, N.v47311.
  unfold R.v6, N.v6.
  rewrite ?node_47310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47312 (s : N.State) (i : N.Inputs) :
  R.v47312 (state s) (inputs i) = Zmod.unsigned (N.v47312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47312 s i)) at 1.
  unfold R.v47312, N.v47312.
  rewrite ?node_14869.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47313 (s : N.State) (i : N.Inputs) :
  R.v47313 (state s) (inputs i) = Zmod.unsigned (N.v47313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47313 s i)) at 1.
  unfold R.v47313, N.v47313.
  unfold R.v6, N.v6.
  rewrite ?node_14952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47314 (s : N.State) (i : N.Inputs) :
  R.v47314 (state s) (inputs i) = Zmod.unsigned (N.v47314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47314 s i)) at 1.
  unfold R.v47314, N.v47314.
  unfold R.v6, N.v6.
  rewrite ?node_14961.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47315 (s : N.State) (i : N.Inputs) :
  R.v47315 (state s) (inputs i) = Zmod.unsigned (N.v47315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47315 s i)) at 1.
  unfold R.v47315, N.v47315.
  rewrite ?node_47312.
  rewrite ?node_47313.
  rewrite ?node_47314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47316 (s : N.State) (i : N.Inputs) :
  R.v47316 (state s) (inputs i) = Zmod.unsigned (N.v47316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47316 s i)) at 1.
  unfold R.v47316, N.v47316.
  rewrite ?node_47311.
  rewrite ?node_47315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47317 (s : N.State) (i : N.Inputs) :
  R.v47317 (state s) (inputs i) = Zmod.unsigned (N.v47317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47317 s i)) at 1.
  unfold R.v47317, N.v47317.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47318 (s : N.State) (i : N.Inputs) :
  R.v47318 (state s) (inputs i) = Zmod.unsigned (N.v47318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47318 s i)) at 1.
  unfold R.v47318, N.v47318.
  rewrite ?node_14860.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47319 (s : N.State) (i : N.Inputs) :
  R.v47319 (state s) (inputs i) = Zmod.unsigned (N.v47319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47319 s i)) at 1.
  unfold R.v47319, N.v47319.
  unfold R.v6, N.v6.
  rewrite ?node_14856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47320 (s : N.State) (i : N.Inputs) :
  R.v47320 (state s) (inputs i) = Zmod.unsigned (N.v47320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47320 s i)) at 1.
  unfold R.v47320, N.v47320.
  unfold R.v6, N.v6.
  rewrite ?node_14853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47321 (s : N.State) (i : N.Inputs) :
  R.v47321 (state s) (inputs i) = Zmod.unsigned (N.v47321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47321 s i)) at 1.
  unfold R.v47321, N.v47321.
  rewrite ?node_47319.
  rewrite ?node_47320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47322 (s : N.State) (i : N.Inputs) :
  R.v47322 (state s) (inputs i) = Zmod.unsigned (N.v47322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47322 s i)) at 1.
  unfold R.v47322, N.v47322.
  unfold R.v16484, N.v16484.
  rewrite ?node_47321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47323 (s : N.State) (i : N.Inputs) :
  R.v47323 (state s) (inputs i) = Zmod.unsigned (N.v47323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47323 s i)) at 1.
  unfold R.v47323, N.v47323.
  rewrite ?node_47318.
  rewrite ?node_47322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47324 (s : N.State) (i : N.Inputs) :
  R.v47324 (state s) (inputs i) = Zmod.unsigned (N.v47324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47324 s i)) at 1.
  unfold R.v47324, N.v47324.
  unfold R.v6, N.v6.
  rewrite ?node_47323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47325 (s : N.State) (i : N.Inputs) :
  R.v47325 (state s) (inputs i) = Zmod.unsigned (N.v47325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47325 s i)) at 1.
  unfold R.v47325, N.v47325.
  rewrite ?node_14861.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47326 (s : N.State) (i : N.Inputs) :
  R.v47326 (state s) (inputs i) = Zmod.unsigned (N.v47326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47326 s i)) at 1.
  unfold R.v47326, N.v47326.
  unfold R.v6, N.v6.
  rewrite ?node_14952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47327 (s : N.State) (i : N.Inputs) :
  R.v47327 (state s) (inputs i) = Zmod.unsigned (N.v47327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47327 s i)) at 1.
  unfold R.v47327, N.v47327.
  rewrite ?node_47325.
  rewrite ?node_47326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47328 (s : N.State) (i : N.Inputs) :
  R.v47328 (state s) (inputs i) = Zmod.unsigned (N.v47328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47328 s i)) at 1.
  unfold R.v47328, N.v47328.
  rewrite ?node_47324.
  rewrite ?node_47327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47329 (s : N.State) (i : N.Inputs) :
  R.v47329 (state s) (inputs i) = Zmod.unsigned (N.v47329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47329 s i)) at 1.
  unfold R.v47329, N.v47329.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47330 (s : N.State) (i : N.Inputs) :
  R.v47330 (state s) (inputs i) = Zmod.unsigned (N.v47330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47330 s i)) at 1.
  unfold R.v47330, N.v47330.
  rewrite ?node_14868.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47331 (s : N.State) (i : N.Inputs) :
  R.v47331 (state s) (inputs i) = Zmod.unsigned (N.v47331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47331 s i)) at 1.
  unfold R.v47331, N.v47331.
  unfold R.v6, N.v6.
  rewrite ?node_14864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47332 (s : N.State) (i : N.Inputs) :
  R.v47332 (state s) (inputs i) = Zmod.unsigned (N.v47332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47332 s i)) at 1.
  unfold R.v47332, N.v47332.
  unfold R.v6, N.v6.
  rewrite ?node_14861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47333 (s : N.State) (i : N.Inputs) :
  R.v47333 (state s) (inputs i) = Zmod.unsigned (N.v47333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47333 s i)) at 1.
  unfold R.v47333, N.v47333.
  rewrite ?node_47331.
  rewrite ?node_47332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47334 (s : N.State) (i : N.Inputs) :
  R.v47334 (state s) (inputs i) = Zmod.unsigned (N.v47334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47334 s i)) at 1.
  unfold R.v47334, N.v47334.
  unfold R.v16484, N.v16484.
  rewrite ?node_47333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47335 (s : N.State) (i : N.Inputs) :
  R.v47335 (state s) (inputs i) = Zmod.unsigned (N.v47335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47335 s i)) at 1.
  unfold R.v47335, N.v47335.
  rewrite ?node_47330.
  rewrite ?node_47334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47336 (s : N.State) (i : N.Inputs) :
  R.v47336 (state s) (inputs i) = Zmod.unsigned (N.v47336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47336 s i)) at 1.
  unfold R.v47336, N.v47336.
  unfold R.v6, N.v6.
  rewrite ?node_47335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47337 (s : N.State) (i : N.Inputs) :
  R.v47337 (state s) (inputs i) = Zmod.unsigned (N.v47337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47337 s i)) at 1.
  unfold R.v47337, N.v47337.
  rewrite ?node_14869.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47338 (s : N.State) (i : N.Inputs) :
  R.v47338 (state s) (inputs i) = Zmod.unsigned (N.v47338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47338 s i)) at 1.
  unfold R.v47338, N.v47338.
  unfold R.v6, N.v6.
  rewrite ?node_14961.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47339 (s : N.State) (i : N.Inputs) :
  R.v47339 (state s) (inputs i) = Zmod.unsigned (N.v47339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47339 s i)) at 1.
  unfold R.v47339, N.v47339.
  rewrite ?node_47337.
  rewrite ?node_47338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47340 (s : N.State) (i : N.Inputs) :
  R.v47340 (state s) (inputs i) = Zmod.unsigned (N.v47340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47340 s i)) at 1.
  unfold R.v47340, N.v47340.
  rewrite ?node_47336.
  rewrite ?node_47339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47341 (s : N.State) (i : N.Inputs) :
  R.v47341 (state s) (inputs i) = Zmod.unsigned (N.v47341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47341 s i)) at 1.
  unfold R.v47341, N.v47341.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47342 (s : N.State) (i : N.Inputs) :
  R.v47342 (state s) (inputs i) = Zmod.unsigned (N.v47342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47342 s i)) at 1.
  unfold R.v47342, N.v47342.
  rewrite ?node_14933.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47343 (s : N.State) (i : N.Inputs) :
  R.v47343 (state s) (inputs i) = Zmod.unsigned (N.v47343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47343 s i)) at 1.
  unfold R.v47343, N.v47343.
  rewrite ?node_14929.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47344 (s : N.State) (i : N.Inputs) :
  R.v47344 (state s) (inputs i) = Zmod.unsigned (N.v47344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47344 s i)) at 1.
  unfold R.v47344, N.v47344.
  rewrite ?node_14921.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47345 (s : N.State) (i : N.Inputs) :
  R.v47345 (state s) (inputs i) = Zmod.unsigned (N.v47345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47345 s i)) at 1.
  unfold R.v47345, N.v47345.
  unfold R.v6, N.v6.
  rewrite ?node_14913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47346 (s : N.State) (i : N.Inputs) :
  R.v47346 (state s) (inputs i) = Zmod.unsigned (N.v47346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47346 s i)) at 1.
  unfold R.v47346, N.v47346.
  unfold R.v6, N.v6.
  rewrite ?node_14906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47347 (s : N.State) (i : N.Inputs) :
  R.v47347 (state s) (inputs i) = Zmod.unsigned (N.v47347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47347 s i)) at 1.
  unfold R.v47347, N.v47347.
  rewrite ?node_47345.
  rewrite ?node_47346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47348 (s : N.State) (i : N.Inputs) :
  R.v47348 (state s) (inputs i) = Zmod.unsigned (N.v47348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47348 s i)) at 1.
  unfold R.v47348, N.v47348.
  unfold R.v16484, N.v16484.
  rewrite ?node_47347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47349 (s : N.State) (i : N.Inputs) :
  R.v47349 (state s) (inputs i) = Zmod.unsigned (N.v47349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47349 s i)) at 1.
  unfold R.v47349, N.v47349.
  rewrite ?node_47342.
  rewrite ?node_47343.
  rewrite ?node_47344.
  rewrite ?node_47348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47350 (s : N.State) (i : N.Inputs) :
  R.v47350 (state s) (inputs i) = Zmod.unsigned (N.v47350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47350 s i)) at 1.
  unfold R.v47350, N.v47350.
  unfold R.v6, N.v6.
  rewrite ?node_47349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47351 (s : N.State) (i : N.Inputs) :
  R.v47351 (state s) (inputs i) = Zmod.unsigned (N.v47351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47351 s i)) at 1.
  unfold R.v47351, N.v47351.
  rewrite ?node_14934.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47352 (s : N.State) (i : N.Inputs) :
  R.v47352 (state s) (inputs i) = Zmod.unsigned (N.v47352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47352 s i)) at 1.
  unfold R.v47352, N.v47352.
  unfold R.v6, N.v6.
  rewrite ?node_15007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47353 (s : N.State) (i : N.Inputs) :
  R.v47353 (state s) (inputs i) = Zmod.unsigned (N.v47353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47353 s i)) at 1.
  unfold R.v47353, N.v47353.
  unfold R.v6, N.v6.
  rewrite ?node_15035.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47354 (s : N.State) (i : N.Inputs) :
  R.v47354 (state s) (inputs i) = Zmod.unsigned (N.v47354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47354 s i)) at 1.
  unfold R.v47354, N.v47354.
  rewrite ?node_47351.
  rewrite ?node_47352.
  rewrite ?node_47353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47355 (s : N.State) (i : N.Inputs) :
  R.v47355 (state s) (inputs i) = Zmod.unsigned (N.v47355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47355 s i)) at 1.
  unfold R.v47355, N.v47355.
  rewrite ?node_47350.
  rewrite ?node_47354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47356 (s : N.State) (i : N.Inputs) :
  R.v47356 (state s) (inputs i) = Zmod.unsigned (N.v47356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47356 s i)) at 1.
  unfold R.v47356, N.v47356.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47357 (s : N.State) (i : N.Inputs) :
  R.v47357 (state s) (inputs i) = Zmod.unsigned (N.v47357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47357 s i)) at 1.
  unfold R.v47357, N.v47357.
  rewrite ?node_14921.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47358 (s : N.State) (i : N.Inputs) :
  R.v47358 (state s) (inputs i) = Zmod.unsigned (N.v47358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47358 s i)) at 1.
  unfold R.v47358, N.v47358.
  unfold R.v6, N.v6.
  rewrite ?node_14913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47359 (s : N.State) (i : N.Inputs) :
  R.v47359 (state s) (inputs i) = Zmod.unsigned (N.v47359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47359 s i)) at 1.
  unfold R.v47359, N.v47359.
  unfold R.v6, N.v6.
  rewrite ?node_14906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47360 (s : N.State) (i : N.Inputs) :
  R.v47360 (state s) (inputs i) = Zmod.unsigned (N.v47360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47360 s i)) at 1.
  unfold R.v47360, N.v47360.
  rewrite ?node_47358.
  rewrite ?node_47359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47361 (s : N.State) (i : N.Inputs) :
  R.v47361 (state s) (inputs i) = Zmod.unsigned (N.v47361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47361 s i)) at 1.
  unfold R.v47361, N.v47361.
  unfold R.v16484, N.v16484.
  rewrite ?node_47360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47362 (s : N.State) (i : N.Inputs) :
  R.v47362 (state s) (inputs i) = Zmod.unsigned (N.v47362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47362 s i)) at 1.
  unfold R.v47362, N.v47362.
  rewrite ?node_47357.
  rewrite ?node_47361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47363 (s : N.State) (i : N.Inputs) :
  R.v47363 (state s) (inputs i) = Zmod.unsigned (N.v47363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47363 s i)) at 1.
  unfold R.v47363, N.v47363.
  unfold R.v6, N.v6.
  rewrite ?node_47362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47364 (s : N.State) (i : N.Inputs) :
  R.v47364 (state s) (inputs i) = Zmod.unsigned (N.v47364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47364 s i)) at 1.
  unfold R.v47364, N.v47364.
  rewrite ?node_14922.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47365 (s : N.State) (i : N.Inputs) :
  R.v47365 (state s) (inputs i) = Zmod.unsigned (N.v47365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47365 s i)) at 1.
  unfold R.v47365, N.v47365.
  unfold R.v6, N.v6.
  rewrite ?node_15007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47366 (s : N.State) (i : N.Inputs) :
  R.v47366 (state s) (inputs i) = Zmod.unsigned (N.v47366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47366 s i)) at 1.
  unfold R.v47366, N.v47366.
  rewrite ?node_47364.
  rewrite ?node_47365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47367 (s : N.State) (i : N.Inputs) :
  R.v47367 (state s) (inputs i) = Zmod.unsigned (N.v47367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47367 s i)) at 1.
  unfold R.v47367, N.v47367.
  rewrite ?node_47363.
  rewrite ?node_47366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47368 (s : N.State) (i : N.Inputs) :
  R.v47368 (state s) (inputs i) = Zmod.unsigned (N.v47368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47368 s i)) at 1.
  unfold R.v47368, N.v47368.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47369 (s : N.State) (i : N.Inputs) :
  R.v47369 (state s) (inputs i) = Zmod.unsigned (N.v47369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47369 s i)) at 1.
  unfold R.v47369, N.v47369.
  rewrite ?node_14933.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47370 (s : N.State) (i : N.Inputs) :
  R.v47370 (state s) (inputs i) = Zmod.unsigned (N.v47370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47370 s i)) at 1.
  unfold R.v47370, N.v47370.
  unfold R.v6, N.v6.
  rewrite ?node_14929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47371 (s : N.State) (i : N.Inputs) :
  R.v47371 (state s) (inputs i) = Zmod.unsigned (N.v47371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47371 s i)) at 1.
  unfold R.v47371, N.v47371.
  unfold R.v6, N.v6.
  rewrite ?node_14922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47372 (s : N.State) (i : N.Inputs) :
  R.v47372 (state s) (inputs i) = Zmod.unsigned (N.v47372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47372 s i)) at 1.
  unfold R.v47372, N.v47372.
  rewrite ?node_47370.
  rewrite ?node_47371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47373 (s : N.State) (i : N.Inputs) :
  R.v47373 (state s) (inputs i) = Zmod.unsigned (N.v47373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47373 s i)) at 1.
  unfold R.v47373, N.v47373.
  unfold R.v16484, N.v16484.
  rewrite ?node_47372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47374 (s : N.State) (i : N.Inputs) :
  R.v47374 (state s) (inputs i) = Zmod.unsigned (N.v47374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47374 s i)) at 1.
  unfold R.v47374, N.v47374.
  rewrite ?node_47369.
  rewrite ?node_47373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47375 (s : N.State) (i : N.Inputs) :
  R.v47375 (state s) (inputs i) = Zmod.unsigned (N.v47375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47375 s i)) at 1.
  unfold R.v47375, N.v47375.
  unfold R.v6, N.v6.
  rewrite ?node_47374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47376 (s : N.State) (i : N.Inputs) :
  R.v47376 (state s) (inputs i) = Zmod.unsigned (N.v47376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47376 s i)) at 1.
  unfold R.v47376, N.v47376.
  rewrite ?node_14934.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47377 (s : N.State) (i : N.Inputs) :
  R.v47377 (state s) (inputs i) = Zmod.unsigned (N.v47377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47377 s i)) at 1.
  unfold R.v47377, N.v47377.
  unfold R.v6, N.v6.
  rewrite ?node_15035.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47378 (s : N.State) (i : N.Inputs) :
  R.v47378 (state s) (inputs i) = Zmod.unsigned (N.v47378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47378 s i)) at 1.
  unfold R.v47378, N.v47378.
  rewrite ?node_47376.
  rewrite ?node_47377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47379 (s : N.State) (i : N.Inputs) :
  R.v47379 (state s) (inputs i) = Zmod.unsigned (N.v47379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47379 s i)) at 1.
  unfold R.v47379, N.v47379.
  rewrite ?node_47375.
  rewrite ?node_47378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47380 (s : N.State) (i : N.Inputs) :
  R.v47380 (state s) (inputs i) = Zmod.unsigned (N.v47380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47380 s i)) at 1.
  unfold R.v47380, N.v47380.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47381 (s : N.State) (i : N.Inputs) :
  R.v47381 (state s) (inputs i) = Zmod.unsigned (N.v47381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47381 s i)) at 1.
  unfold R.v47381, N.v47381.
  rewrite ?node_14952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47382 (s : N.State) (i : N.Inputs) :
  R.v47382 (state s) (inputs i) = Zmod.unsigned (N.v47382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47382 s i)) at 1.
  unfold R.v47382, N.v47382.
  rewrite ?node_14948.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47383 (s : N.State) (i : N.Inputs) :
  R.v47383 (state s) (inputs i) = Zmod.unsigned (N.v47383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47383 s i)) at 1.
  unfold R.v47383, N.v47383.
  rewrite ?node_14944.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47384 (s : N.State) (i : N.Inputs) :
  R.v47384 (state s) (inputs i) = Zmod.unsigned (N.v47384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47384 s i)) at 1.
  unfold R.v47384, N.v47384.
  unfold R.v6, N.v6.
  rewrite ?node_14940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47385 (s : N.State) (i : N.Inputs) :
  R.v47385 (state s) (inputs i) = Zmod.unsigned (N.v47385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47385 s i)) at 1.
  unfold R.v47385, N.v47385.
  unfold R.v6, N.v6.
  rewrite ?node_14937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47386 (s : N.State) (i : N.Inputs) :
  R.v47386 (state s) (inputs i) = Zmod.unsigned (N.v47386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47386 s i)) at 1.
  unfold R.v47386, N.v47386.
  rewrite ?node_47384.
  rewrite ?node_47385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47387 (s : N.State) (i : N.Inputs) :
  R.v47387 (state s) (inputs i) = Zmod.unsigned (N.v47387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47387 s i)) at 1.
  unfold R.v47387, N.v47387.
  unfold R.v16484, N.v16484.
  rewrite ?node_47386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47388 (s : N.State) (i : N.Inputs) :
  R.v47388 (state s) (inputs i) = Zmod.unsigned (N.v47388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47388 s i)) at 1.
  unfold R.v47388, N.v47388.
  rewrite ?node_47381.
  rewrite ?node_47382.
  rewrite ?node_47383.
  rewrite ?node_47387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47389 (s : N.State) (i : N.Inputs) :
  R.v47389 (state s) (inputs i) = Zmod.unsigned (N.v47389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47389 s i)) at 1.
  unfold R.v47389, N.v47389.
  unfold R.v6, N.v6.
  rewrite ?node_47388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47390 (s : N.State) (i : N.Inputs) :
  R.v47390 (state s) (inputs i) = Zmod.unsigned (N.v47390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47390 s i)) at 1.
  unfold R.v47390, N.v47390.
  rewrite ?node_14953.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47391 (s : N.State) (i : N.Inputs) :
  R.v47391 (state s) (inputs i) = Zmod.unsigned (N.v47391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47391 s i)) at 1.
  unfold R.v47391, N.v47391.
  unfold R.v6, N.v6.
  rewrite ?node_15026.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47392 (s : N.State) (i : N.Inputs) :
  R.v47392 (state s) (inputs i) = Zmod.unsigned (N.v47392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47392 s i)) at 1.
  unfold R.v47392, N.v47392.
  unfold R.v6, N.v6.
  rewrite ?node_15043.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47393 (s : N.State) (i : N.Inputs) :
  R.v47393 (state s) (inputs i) = Zmod.unsigned (N.v47393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47393 s i)) at 1.
  unfold R.v47393, N.v47393.
  rewrite ?node_47390.
  rewrite ?node_47391.
  rewrite ?node_47392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47394 (s : N.State) (i : N.Inputs) :
  R.v47394 (state s) (inputs i) = Zmod.unsigned (N.v47394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47394 s i)) at 1.
  unfold R.v47394, N.v47394.
  rewrite ?node_47389.
  rewrite ?node_47393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47395 (s : N.State) (i : N.Inputs) :
  R.v47395 (state s) (inputs i) = Zmod.unsigned (N.v47395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47395 s i)) at 1.
  unfold R.v47395, N.v47395.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47396 (s : N.State) (i : N.Inputs) :
  R.v47396 (state s) (inputs i) = Zmod.unsigned (N.v47396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47396 s i)) at 1.
  unfold R.v47396, N.v47396.
  rewrite ?node_14944.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47397 (s : N.State) (i : N.Inputs) :
  R.v47397 (state s) (inputs i) = Zmod.unsigned (N.v47397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47397 s i)) at 1.
  unfold R.v47397, N.v47397.
  unfold R.v6, N.v6.
  rewrite ?node_14940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47398 (s : N.State) (i : N.Inputs) :
  R.v47398 (state s) (inputs i) = Zmod.unsigned (N.v47398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47398 s i)) at 1.
  unfold R.v47398, N.v47398.
  unfold R.v6, N.v6.
  rewrite ?node_14937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47399 (s : N.State) (i : N.Inputs) :
  R.v47399 (state s) (inputs i) = Zmod.unsigned (N.v47399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47399 s i)) at 1.
  unfold R.v47399, N.v47399.
  rewrite ?node_47397.
  rewrite ?node_47398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47400 (s : N.State) (i : N.Inputs) :
  R.v47400 (state s) (inputs i) = Zmod.unsigned (N.v47400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47400 s i)) at 1.
  unfold R.v47400, N.v47400.
  unfold R.v16484, N.v16484.
  rewrite ?node_47399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47401 (s : N.State) (i : N.Inputs) :
  R.v47401 (state s) (inputs i) = Zmod.unsigned (N.v47401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47401 s i)) at 1.
  unfold R.v47401, N.v47401.
  rewrite ?node_47396.
  rewrite ?node_47400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47402 (s : N.State) (i : N.Inputs) :
  R.v47402 (state s) (inputs i) = Zmod.unsigned (N.v47402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47402 s i)) at 1.
  unfold R.v47402, N.v47402.
  unfold R.v6, N.v6.
  rewrite ?node_47401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47403 (s : N.State) (i : N.Inputs) :
  R.v47403 (state s) (inputs i) = Zmod.unsigned (N.v47403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47403 s i)) at 1.
  unfold R.v47403, N.v47403.
  rewrite ?node_14945.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47404 (s : N.State) (i : N.Inputs) :
  R.v47404 (state s) (inputs i) = Zmod.unsigned (N.v47404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47404 s i)) at 1.
  unfold R.v47404, N.v47404.
  unfold R.v6, N.v6.
  rewrite ?node_15026.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47405 (s : N.State) (i : N.Inputs) :
  R.v47405 (state s) (inputs i) = Zmod.unsigned (N.v47405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47405 s i)) at 1.
  unfold R.v47405, N.v47405.
  rewrite ?node_47403.
  rewrite ?node_47404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47406 (s : N.State) (i : N.Inputs) :
  R.v47406 (state s) (inputs i) = Zmod.unsigned (N.v47406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47406 s i)) at 1.
  unfold R.v47406, N.v47406.
  rewrite ?node_47402.
  rewrite ?node_47405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47407 (s : N.State) (i : N.Inputs) :
  R.v47407 (state s) (inputs i) = Zmod.unsigned (N.v47407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47407 s i)) at 1.
  unfold R.v47407, N.v47407.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47408 (s : N.State) (i : N.Inputs) :
  R.v47408 (state s) (inputs i) = Zmod.unsigned (N.v47408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47408 s i)) at 1.
  unfold R.v47408, N.v47408.
  rewrite ?node_14952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47409 (s : N.State) (i : N.Inputs) :
  R.v47409 (state s) (inputs i) = Zmod.unsigned (N.v47409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47409 s i)) at 1.
  unfold R.v47409, N.v47409.
  unfold R.v6, N.v6.
  rewrite ?node_14948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47410 (s : N.State) (i : N.Inputs) :
  R.v47410 (state s) (inputs i) = Zmod.unsigned (N.v47410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47410 s i)) at 1.
  unfold R.v47410, N.v47410.
  unfold R.v6, N.v6.
  rewrite ?node_14945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47411 (s : N.State) (i : N.Inputs) :
  R.v47411 (state s) (inputs i) = Zmod.unsigned (N.v47411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47411 s i)) at 1.
  unfold R.v47411, N.v47411.
  rewrite ?node_47409.
  rewrite ?node_47410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47412 (s : N.State) (i : N.Inputs) :
  R.v47412 (state s) (inputs i) = Zmod.unsigned (N.v47412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47412 s i)) at 1.
  unfold R.v47412, N.v47412.
  unfold R.v16484, N.v16484.
  rewrite ?node_47411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47413 (s : N.State) (i : N.Inputs) :
  R.v47413 (state s) (inputs i) = Zmod.unsigned (N.v47413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47413 s i)) at 1.
  unfold R.v47413, N.v47413.
  rewrite ?node_47408.
  rewrite ?node_47412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47414 (s : N.State) (i : N.Inputs) :
  R.v47414 (state s) (inputs i) = Zmod.unsigned (N.v47414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47414 s i)) at 1.
  unfold R.v47414, N.v47414.
  unfold R.v6, N.v6.
  rewrite ?node_47413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47415 (s : N.State) (i : N.Inputs) :
  R.v47415 (state s) (inputs i) = Zmod.unsigned (N.v47415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47415 s i)) at 1.
  unfold R.v47415, N.v47415.
  rewrite ?node_14953.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47416 (s : N.State) (i : N.Inputs) :
  R.v47416 (state s) (inputs i) = Zmod.unsigned (N.v47416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47416 s i)) at 1.
  unfold R.v47416, N.v47416.
  unfold R.v6, N.v6.
  rewrite ?node_15043.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47417 (s : N.State) (i : N.Inputs) :
  R.v47417 (state s) (inputs i) = Zmod.unsigned (N.v47417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47417 s i)) at 1.
  unfold R.v47417, N.v47417.
  rewrite ?node_47415.
  rewrite ?node_47416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47418 (s : N.State) (i : N.Inputs) :
  R.v47418 (state s) (inputs i) = Zmod.unsigned (N.v47418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47418 s i)) at 1.
  unfold R.v47418, N.v47418.
  rewrite ?node_47414.
  rewrite ?node_47417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47419 (s : N.State) (i : N.Inputs) :
  R.v47419 (state s) (inputs i) = Zmod.unsigned (N.v47419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47419 s i)) at 1.
  unfold R.v47419, N.v47419.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47420 (s : N.State) (i : N.Inputs) :
  R.v47420 (state s) (inputs i) = Zmod.unsigned (N.v47420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47420 s i)) at 1.
  unfold R.v47420, N.v47420.
  rewrite ?node_15007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47421 (s : N.State) (i : N.Inputs) :
  R.v47421 (state s) (inputs i) = Zmod.unsigned (N.v47421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47421 s i)) at 1.
  unfold R.v47421, N.v47421.
  rewrite ?node_15003.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47422 (s : N.State) (i : N.Inputs) :
  R.v47422 (state s) (inputs i) = Zmod.unsigned (N.v47422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47422 s i)) at 1.
  unfold R.v47422, N.v47422.
  rewrite ?node_15000.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47423 (s : N.State) (i : N.Inputs) :
  R.v47423 (state s) (inputs i) = Zmod.unsigned (N.v47423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47423 s i)) at 1.
  unfold R.v47423, N.v47423.
  unfold R.v6, N.v6.
  rewrite ?node_14992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47424 (s : N.State) (i : N.Inputs) :
  R.v47424 (state s) (inputs i) = Zmod.unsigned (N.v47424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47424 s i)) at 1.
  unfold R.v47424, N.v47424.
  unfold R.v6, N.v6.
  rewrite ?node_14985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47425 (s : N.State) (i : N.Inputs) :
  R.v47425 (state s) (inputs i) = Zmod.unsigned (N.v47425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47425 s i)) at 1.
  unfold R.v47425, N.v47425.
  rewrite ?node_47423.
  rewrite ?node_47424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47426 (s : N.State) (i : N.Inputs) :
  R.v47426 (state s) (inputs i) = Zmod.unsigned (N.v47426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47426 s i)) at 1.
  unfold R.v47426, N.v47426.
  unfold R.v16484, N.v16484.
  rewrite ?node_47425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47427 (s : N.State) (i : N.Inputs) :
  R.v47427 (state s) (inputs i) = Zmod.unsigned (N.v47427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47427 s i)) at 1.
  unfold R.v47427, N.v47427.
  rewrite ?node_47420.
  rewrite ?node_47421.
  rewrite ?node_47422.
  rewrite ?node_47426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47428 (s : N.State) (i : N.Inputs) :
  R.v47428 (state s) (inputs i) = Zmod.unsigned (N.v47428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47428 s i)) at 1.
  unfold R.v47428, N.v47428.
  unfold R.v6, N.v6.
  rewrite ?node_47427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47429 (s : N.State) (i : N.Inputs) :
  R.v47429 (state s) (inputs i) = Zmod.unsigned (N.v47429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47429 s i)) at 1.
  unfold R.v47429, N.v47429.
  rewrite ?node_15008.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47430 (s : N.State) (i : N.Inputs) :
  R.v47430 (state s) (inputs i) = Zmod.unsigned (N.v47430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47430 s i)) at 1.
  unfold R.v47430, N.v47430.
  unfold R.v6, N.v6.
  rewrite ?node_15082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47431 (s : N.State) (i : N.Inputs) :
  R.v47431 (state s) (inputs i) = Zmod.unsigned (N.v47431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47431 s i)) at 1.
  unfold R.v47431, N.v47431.
  unfold R.v6, N.v6.
  rewrite ?node_15106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47432 (s : N.State) (i : N.Inputs) :
  R.v47432 (state s) (inputs i) = Zmod.unsigned (N.v47432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47432 s i)) at 1.
  unfold R.v47432, N.v47432.
  rewrite ?node_47429.
  rewrite ?node_47430.
  rewrite ?node_47431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47433 (s : N.State) (i : N.Inputs) :
  R.v47433 (state s) (inputs i) = Zmod.unsigned (N.v47433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47433 s i)) at 1.
  unfold R.v47433, N.v47433.
  rewrite ?node_47428.
  rewrite ?node_47432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47434 (s : N.State) (i : N.Inputs) :
  R.v47434 (state s) (inputs i) = Zmod.unsigned (N.v47434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47434 s i)) at 1.
  unfold R.v47434, N.v47434.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47435 (s : N.State) (i : N.Inputs) :
  R.v47435 (state s) (inputs i) = Zmod.unsigned (N.v47435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47435 s i)) at 1.
  unfold R.v47435, N.v47435.
  rewrite ?node_15000.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47436 (s : N.State) (i : N.Inputs) :
  R.v47436 (state s) (inputs i) = Zmod.unsigned (N.v47436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47436 s i)) at 1.
  unfold R.v47436, N.v47436.
  unfold R.v6, N.v6.
  rewrite ?node_14992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47437 (s : N.State) (i : N.Inputs) :
  R.v47437 (state s) (inputs i) = Zmod.unsigned (N.v47437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47437 s i)) at 1.
  unfold R.v47437, N.v47437.
  unfold R.v6, N.v6.
  rewrite ?node_14985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47438 (s : N.State) (i : N.Inputs) :
  R.v47438 (state s) (inputs i) = Zmod.unsigned (N.v47438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47438 s i)) at 1.
  unfold R.v47438, N.v47438.
  rewrite ?node_47436.
  rewrite ?node_47437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47439 (s : N.State) (i : N.Inputs) :
  R.v47439 (state s) (inputs i) = Zmod.unsigned (N.v47439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47439 s i)) at 1.
  unfold R.v47439, N.v47439.
  unfold R.v16484, N.v16484.
  rewrite ?node_47438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47440 (s : N.State) (i : N.Inputs) :
  R.v47440 (state s) (inputs i) = Zmod.unsigned (N.v47440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47440 s i)) at 1.
  unfold R.v47440, N.v47440.
  rewrite ?node_47435.
  rewrite ?node_47439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47441 (s : N.State) (i : N.Inputs) :
  R.v47441 (state s) (inputs i) = Zmod.unsigned (N.v47441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47441 s i)) at 1.
  unfold R.v47441, N.v47441.
  unfold R.v6, N.v6.
  rewrite ?node_47440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47442 (s : N.State) (i : N.Inputs) :
  R.v47442 (state s) (inputs i) = Zmod.unsigned (N.v47442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47442 s i)) at 1.
  unfold R.v47442, N.v47442.
  rewrite ?node_15001.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47443 (s : N.State) (i : N.Inputs) :
  R.v47443 (state s) (inputs i) = Zmod.unsigned (N.v47443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47443 s i)) at 1.
  unfold R.v47443, N.v47443.
  unfold R.v6, N.v6.
  rewrite ?node_15082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47444 (s : N.State) (i : N.Inputs) :
  R.v47444 (state s) (inputs i) = Zmod.unsigned (N.v47444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47444 s i)) at 1.
  unfold R.v47444, N.v47444.
  rewrite ?node_47442.
  rewrite ?node_47443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47445 (s : N.State) (i : N.Inputs) :
  R.v47445 (state s) (inputs i) = Zmod.unsigned (N.v47445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47445 s i)) at 1.
  unfold R.v47445, N.v47445.
  rewrite ?node_47441.
  rewrite ?node_47444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47446 (s : N.State) (i : N.Inputs) :
  R.v47446 (state s) (inputs i) = Zmod.unsigned (N.v47446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47446 s i)) at 1.
  unfold R.v47446, N.v47446.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47447 (s : N.State) (i : N.Inputs) :
  R.v47447 (state s) (inputs i) = Zmod.unsigned (N.v47447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47447 s i)) at 1.
  unfold R.v47447, N.v47447.
  rewrite ?node_15007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47448 (s : N.State) (i : N.Inputs) :
  R.v47448 (state s) (inputs i) = Zmod.unsigned (N.v47448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47448 s i)) at 1.
  unfold R.v47448, N.v47448.
  unfold R.v6, N.v6.
  rewrite ?node_15003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47449 (s : N.State) (i : N.Inputs) :
  R.v47449 (state s) (inputs i) = Zmod.unsigned (N.v47449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47449 s i)) at 1.
  unfold R.v47449, N.v47449.
  unfold R.v6, N.v6.
  rewrite ?node_15001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47450 (s : N.State) (i : N.Inputs) :
  R.v47450 (state s) (inputs i) = Zmod.unsigned (N.v47450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47450 s i)) at 1.
  unfold R.v47450, N.v47450.
  rewrite ?node_47448.
  rewrite ?node_47449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47451 (s : N.State) (i : N.Inputs) :
  R.v47451 (state s) (inputs i) = Zmod.unsigned (N.v47451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47451 s i)) at 1.
  unfold R.v47451, N.v47451.
  unfold R.v16484, N.v16484.
  rewrite ?node_47450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47452 (s : N.State) (i : N.Inputs) :
  R.v47452 (state s) (inputs i) = Zmod.unsigned (N.v47452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47452 s i)) at 1.
  unfold R.v47452, N.v47452.
  rewrite ?node_47447.
  rewrite ?node_47451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47453 (s : N.State) (i : N.Inputs) :
  R.v47453 (state s) (inputs i) = Zmod.unsigned (N.v47453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47453 s i)) at 1.
  unfold R.v47453, N.v47453.
  unfold R.v6, N.v6.
  rewrite ?node_47452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47454 (s : N.State) (i : N.Inputs) :
  R.v47454 (state s) (inputs i) = Zmod.unsigned (N.v47454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47454 s i)) at 1.
  unfold R.v47454, N.v47454.
  rewrite ?node_15008.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47455 (s : N.State) (i : N.Inputs) :
  R.v47455 (state s) (inputs i) = Zmod.unsigned (N.v47455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47455 s i)) at 1.
  unfold R.v47455, N.v47455.
  unfold R.v6, N.v6.
  rewrite ?node_15106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47456 (s : N.State) (i : N.Inputs) :
  R.v47456 (state s) (inputs i) = Zmod.unsigned (N.v47456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47456 s i)) at 1.
  unfold R.v47456, N.v47456.
  rewrite ?node_47454.
  rewrite ?node_47455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47457 (s : N.State) (i : N.Inputs) :
  R.v47457 (state s) (inputs i) = Zmod.unsigned (N.v47457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47457 s i)) at 1.
  unfold R.v47457, N.v47457.
  rewrite ?node_47453.
  rewrite ?node_47456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47458 (s : N.State) (i : N.Inputs) :
  R.v47458 (state s) (inputs i) = Zmod.unsigned (N.v47458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47458 s i)) at 1.
  unfold R.v47458, N.v47458.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47459 (s : N.State) (i : N.Inputs) :
  R.v47459 (state s) (inputs i) = Zmod.unsigned (N.v47459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47459 s i)) at 1.
  unfold R.v47459, N.v47459.
  rewrite ?node_15026.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47460 (s : N.State) (i : N.Inputs) :
  R.v47460 (state s) (inputs i) = Zmod.unsigned (N.v47460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47460 s i)) at 1.
  unfold R.v47460, N.v47460.
  rewrite ?node_15022.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47461 (s : N.State) (i : N.Inputs) :
  R.v47461 (state s) (inputs i) = Zmod.unsigned (N.v47461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47461 s i)) at 1.
  unfold R.v47461, N.v47461.
  rewrite ?node_15018.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47462 (s : N.State) (i : N.Inputs) :
  R.v47462 (state s) (inputs i) = Zmod.unsigned (N.v47462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47462 s i)) at 1.
  unfold R.v47462, N.v47462.
  unfold R.v6, N.v6.
  rewrite ?node_15014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47463 (s : N.State) (i : N.Inputs) :
  R.v47463 (state s) (inputs i) = Zmod.unsigned (N.v47463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47463 s i)) at 1.
  unfold R.v47463, N.v47463.
  unfold R.v6, N.v6.
  rewrite ?node_15011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47464 (s : N.State) (i : N.Inputs) :
  R.v47464 (state s) (inputs i) = Zmod.unsigned (N.v47464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47464 s i)) at 1.
  unfold R.v47464, N.v47464.
  rewrite ?node_47462.
  rewrite ?node_47463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47465 (s : N.State) (i : N.Inputs) :
  R.v47465 (state s) (inputs i) = Zmod.unsigned (N.v47465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47465 s i)) at 1.
  unfold R.v47465, N.v47465.
  unfold R.v16484, N.v16484.
  rewrite ?node_47464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47466 (s : N.State) (i : N.Inputs) :
  R.v47466 (state s) (inputs i) = Zmod.unsigned (N.v47466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47466 s i)) at 1.
  unfold R.v47466, N.v47466.
  rewrite ?node_47459.
  rewrite ?node_47460.
  rewrite ?node_47461.
  rewrite ?node_47465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47467 (s : N.State) (i : N.Inputs) :
  R.v47467 (state s) (inputs i) = Zmod.unsigned (N.v47467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47467 s i)) at 1.
  unfold R.v47467, N.v47467.
  unfold R.v6, N.v6.
  rewrite ?node_47466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47468 (s : N.State) (i : N.Inputs) :
  R.v47468 (state s) (inputs i) = Zmod.unsigned (N.v47468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47468 s i)) at 1.
  unfold R.v47468, N.v47468.
  rewrite ?node_15027.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47469 (s : N.State) (i : N.Inputs) :
  R.v47469 (state s) (inputs i) = Zmod.unsigned (N.v47469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47469 s i)) at 1.
  unfold R.v47469, N.v47469.
  unfold R.v6, N.v6.
  rewrite ?node_15101.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47470 (s : N.State) (i : N.Inputs) :
  R.v47470 (state s) (inputs i) = Zmod.unsigned (N.v47470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47470 s i)) at 1.
  unfold R.v47470, N.v47470.
  unfold R.v6, N.v6.
  rewrite ?node_15110.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47471 (s : N.State) (i : N.Inputs) :
  R.v47471 (state s) (inputs i) = Zmod.unsigned (N.v47471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47471 s i)) at 1.
  unfold R.v47471, N.v47471.
  rewrite ?node_47468.
  rewrite ?node_47469.
  rewrite ?node_47470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47472 (s : N.State) (i : N.Inputs) :
  R.v47472 (state s) (inputs i) = Zmod.unsigned (N.v47472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47472 s i)) at 1.
  unfold R.v47472, N.v47472.
  rewrite ?node_47467.
  rewrite ?node_47471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47473 (s : N.State) (i : N.Inputs) :
  R.v47473 (state s) (inputs i) = Zmod.unsigned (N.v47473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47473 s i)) at 1.
  unfold R.v47473, N.v47473.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47474 (s : N.State) (i : N.Inputs) :
  R.v47474 (state s) (inputs i) = Zmod.unsigned (N.v47474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47474 s i)) at 1.
  unfold R.v47474, N.v47474.
  rewrite ?node_15018.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47475 (s : N.State) (i : N.Inputs) :
  R.v47475 (state s) (inputs i) = Zmod.unsigned (N.v47475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47475 s i)) at 1.
  unfold R.v47475, N.v47475.
  unfold R.v6, N.v6.
  rewrite ?node_15014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47476 (s : N.State) (i : N.Inputs) :
  R.v47476 (state s) (inputs i) = Zmod.unsigned (N.v47476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47476 s i)) at 1.
  unfold R.v47476, N.v47476.
  unfold R.v6, N.v6.
  rewrite ?node_15011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47477 (s : N.State) (i : N.Inputs) :
  R.v47477 (state s) (inputs i) = Zmod.unsigned (N.v47477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47477 s i)) at 1.
  unfold R.v47477, N.v47477.
  rewrite ?node_47475.
  rewrite ?node_47476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47478 (s : N.State) (i : N.Inputs) :
  R.v47478 (state s) (inputs i) = Zmod.unsigned (N.v47478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47478 s i)) at 1.
  unfold R.v47478, N.v47478.
  unfold R.v16484, N.v16484.
  rewrite ?node_47477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47479 (s : N.State) (i : N.Inputs) :
  R.v47479 (state s) (inputs i) = Zmod.unsigned (N.v47479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47479 s i)) at 1.
  unfold R.v47479, N.v47479.
  rewrite ?node_47474.
  rewrite ?node_47478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47480 (s : N.State) (i : N.Inputs) :
  R.v47480 (state s) (inputs i) = Zmod.unsigned (N.v47480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47480 s i)) at 1.
  unfold R.v47480, N.v47480.
  unfold R.v6, N.v6.
  rewrite ?node_47479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47481 (s : N.State) (i : N.Inputs) :
  R.v47481 (state s) (inputs i) = Zmod.unsigned (N.v47481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47481 s i)) at 1.
  unfold R.v47481, N.v47481.
  rewrite ?node_15019.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47482 (s : N.State) (i : N.Inputs) :
  R.v47482 (state s) (inputs i) = Zmod.unsigned (N.v47482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47482 s i)) at 1.
  unfold R.v47482, N.v47482.
  unfold R.v6, N.v6.
  rewrite ?node_15101.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47483 (s : N.State) (i : N.Inputs) :
  R.v47483 (state s) (inputs i) = Zmod.unsigned (N.v47483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47483 s i)) at 1.
  unfold R.v47483, N.v47483.
  rewrite ?node_47481.
  rewrite ?node_47482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47484 (s : N.State) (i : N.Inputs) :
  R.v47484 (state s) (inputs i) = Zmod.unsigned (N.v47484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47484 s i)) at 1.
  unfold R.v47484, N.v47484.
  rewrite ?node_47480.
  rewrite ?node_47483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47485 (s : N.State) (i : N.Inputs) :
  R.v47485 (state s) (inputs i) = Zmod.unsigned (N.v47485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47485 s i)) at 1.
  unfold R.v47485, N.v47485.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47486 (s : N.State) (i : N.Inputs) :
  R.v47486 (state s) (inputs i) = Zmod.unsigned (N.v47486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47486 s i)) at 1.
  unfold R.v47486, N.v47486.
  rewrite ?node_15026.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47487 (s : N.State) (i : N.Inputs) :
  R.v47487 (state s) (inputs i) = Zmod.unsigned (N.v47487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47487 s i)) at 1.
  unfold R.v47487, N.v47487.
  unfold R.v6, N.v6.
  rewrite ?node_15022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47488 (s : N.State) (i : N.Inputs) :
  R.v47488 (state s) (inputs i) = Zmod.unsigned (N.v47488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47488 s i)) at 1.
  unfold R.v47488, N.v47488.
  unfold R.v6, N.v6.
  rewrite ?node_15019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47489 (s : N.State) (i : N.Inputs) :
  R.v47489 (state s) (inputs i) = Zmod.unsigned (N.v47489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47489 s i)) at 1.
  unfold R.v47489, N.v47489.
  rewrite ?node_47487.
  rewrite ?node_47488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47490 (s : N.State) (i : N.Inputs) :
  R.v47490 (state s) (inputs i) = Zmod.unsigned (N.v47490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47490 s i)) at 1.
  unfold R.v47490, N.v47490.
  unfold R.v16484, N.v16484.
  rewrite ?node_47489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47491 (s : N.State) (i : N.Inputs) :
  R.v47491 (state s) (inputs i) = Zmod.unsigned (N.v47491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47491 s i)) at 1.
  unfold R.v47491, N.v47491.
  rewrite ?node_47486.
  rewrite ?node_47490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47492 (s : N.State) (i : N.Inputs) :
  R.v47492 (state s) (inputs i) = Zmod.unsigned (N.v47492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47492 s i)) at 1.
  unfold R.v47492, N.v47492.
  unfold R.v6, N.v6.
  rewrite ?node_47491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47493 (s : N.State) (i : N.Inputs) :
  R.v47493 (state s) (inputs i) = Zmod.unsigned (N.v47493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47493 s i)) at 1.
  unfold R.v47493, N.v47493.
  rewrite ?node_15027.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47494 (s : N.State) (i : N.Inputs) :
  R.v47494 (state s) (inputs i) = Zmod.unsigned (N.v47494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47494 s i)) at 1.
  unfold R.v47494, N.v47494.
  unfold R.v6, N.v6.
  rewrite ?node_15110.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47495 (s : N.State) (i : N.Inputs) :
  R.v47495 (state s) (inputs i) = Zmod.unsigned (N.v47495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47495 s i)) at 1.
  unfold R.v47495, N.v47495.
  rewrite ?node_47493.
  rewrite ?node_47494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47496 (s : N.State) (i : N.Inputs) :
  R.v47496 (state s) (inputs i) = Zmod.unsigned (N.v47496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47496 s i)) at 1.
  unfold R.v47496, N.v47496.
  rewrite ?node_47492.
  rewrite ?node_47495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47497 (s : N.State) (i : N.Inputs) :
  R.v47497 (state s) (inputs i) = Zmod.unsigned (N.v47497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47497 s i)) at 1.
  unfold R.v47497, N.v47497.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47498 (s : N.State) (i : N.Inputs) :
  R.v47498 (state s) (inputs i) = Zmod.unsigned (N.v47498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47498 s i)) at 1.
  unfold R.v47498, N.v47498.
  rewrite ?node_15082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47499 (s : N.State) (i : N.Inputs) :
  R.v47499 (state s) (inputs i) = Zmod.unsigned (N.v47499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47499 s i)) at 1.
  unfold R.v47499, N.v47499.
  rewrite ?node_15078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47500 (s : N.State) (i : N.Inputs) :
  R.v47500 (state s) (inputs i) = Zmod.unsigned (N.v47500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47500 s i)) at 1.
  unfold R.v47500, N.v47500.
  rewrite ?node_15075.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47501 (s : N.State) (i : N.Inputs) :
  R.v47501 (state s) (inputs i) = Zmod.unsigned (N.v47501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47501 s i)) at 1.
  unfold R.v47501, N.v47501.
  unfold R.v6, N.v6.
  rewrite ?node_15067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47502 (s : N.State) (i : N.Inputs) :
  R.v47502 (state s) (inputs i) = Zmod.unsigned (N.v47502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47502 s i)) at 1.
  unfold R.v47502, N.v47502.
  unfold R.v6, N.v6.
  rewrite ?node_15060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47503 (s : N.State) (i : N.Inputs) :
  R.v47503 (state s) (inputs i) = Zmod.unsigned (N.v47503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47503 s i)) at 1.
  unfold R.v47503, N.v47503.
  rewrite ?node_47501.
  rewrite ?node_47502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47504 (s : N.State) (i : N.Inputs) :
  R.v47504 (state s) (inputs i) = Zmod.unsigned (N.v47504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47504 s i)) at 1.
  unfold R.v47504, N.v47504.
  unfold R.v16484, N.v16484.
  rewrite ?node_47503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47505 (s : N.State) (i : N.Inputs) :
  R.v47505 (state s) (inputs i) = Zmod.unsigned (N.v47505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47505 s i)) at 1.
  unfold R.v47505, N.v47505.
  rewrite ?node_47498.
  rewrite ?node_47499.
  rewrite ?node_47500.
  rewrite ?node_47504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47506 (s : N.State) (i : N.Inputs) :
  R.v47506 (state s) (inputs i) = Zmod.unsigned (N.v47506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47506 s i)) at 1.
  unfold R.v47506, N.v47506.
  unfold R.v6, N.v6.
  rewrite ?node_47505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47507 (s : N.State) (i : N.Inputs) :
  R.v47507 (state s) (inputs i) = Zmod.unsigned (N.v47507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47507 s i)) at 1.
  unfold R.v47507, N.v47507.
  rewrite ?node_15083.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47508 (s : N.State) (i : N.Inputs) :
  R.v47508 (state s) (inputs i) = Zmod.unsigned (N.v47508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47508 s i)) at 1.
  unfold R.v47508, N.v47508.
  unfold R.v6, N.v6.
  rewrite ?node_15153.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47509 (s : N.State) (i : N.Inputs) :
  R.v47509 (state s) (inputs i) = Zmod.unsigned (N.v47509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47509 s i)) at 1.
  unfold R.v47509, N.v47509.
  unfold R.v6, N.v6.
  rewrite ?node_15177.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47510 (s : N.State) (i : N.Inputs) :
  R.v47510 (state s) (inputs i) = Zmod.unsigned (N.v47510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47510 s i)) at 1.
  unfold R.v47510, N.v47510.
  rewrite ?node_47507.
  rewrite ?node_47508.
  rewrite ?node_47509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47511 (s : N.State) (i : N.Inputs) :
  R.v47511 (state s) (inputs i) = Zmod.unsigned (N.v47511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47511 s i)) at 1.
  unfold R.v47511, N.v47511.
  rewrite ?node_47506.
  rewrite ?node_47510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47512 (s : N.State) (i : N.Inputs) :
  R.v47512 (state s) (inputs i) = Zmod.unsigned (N.v47512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47512 s i)) at 1.
  unfold R.v47512, N.v47512.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47513 (s : N.State) (i : N.Inputs) :
  R.v47513 (state s) (inputs i) = Zmod.unsigned (N.v47513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47513 s i)) at 1.
  unfold R.v47513, N.v47513.
  rewrite ?node_15075.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47514 (s : N.State) (i : N.Inputs) :
  R.v47514 (state s) (inputs i) = Zmod.unsigned (N.v47514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47514 s i)) at 1.
  unfold R.v47514, N.v47514.
  unfold R.v6, N.v6.
  rewrite ?node_15067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47515 (s : N.State) (i : N.Inputs) :
  R.v47515 (state s) (inputs i) = Zmod.unsigned (N.v47515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47515 s i)) at 1.
  unfold R.v47515, N.v47515.
  unfold R.v6, N.v6.
  rewrite ?node_15060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47516 (s : N.State) (i : N.Inputs) :
  R.v47516 (state s) (inputs i) = Zmod.unsigned (N.v47516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47516 s i)) at 1.
  unfold R.v47516, N.v47516.
  rewrite ?node_47514.
  rewrite ?node_47515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47517 (s : N.State) (i : N.Inputs) :
  R.v47517 (state s) (inputs i) = Zmod.unsigned (N.v47517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47517 s i)) at 1.
  unfold R.v47517, N.v47517.
  unfold R.v16484, N.v16484.
  rewrite ?node_47516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47518 (s : N.State) (i : N.Inputs) :
  R.v47518 (state s) (inputs i) = Zmod.unsigned (N.v47518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47518 s i)) at 1.
  unfold R.v47518, N.v47518.
  rewrite ?node_47513.
  rewrite ?node_47517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47519 (s : N.State) (i : N.Inputs) :
  R.v47519 (state s) (inputs i) = Zmod.unsigned (N.v47519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47519 s i)) at 1.
  unfold R.v47519, N.v47519.
  unfold R.v6, N.v6.
  rewrite ?node_47518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47520 (s : N.State) (i : N.Inputs) :
  R.v47520 (state s) (inputs i) = Zmod.unsigned (N.v47520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47520 s i)) at 1.
  unfold R.v47520, N.v47520.
  rewrite ?node_15076.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47521 (s : N.State) (i : N.Inputs) :
  R.v47521 (state s) (inputs i) = Zmod.unsigned (N.v47521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47521 s i)) at 1.
  unfold R.v47521, N.v47521.
  unfold R.v6, N.v6.
  rewrite ?node_15153.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47522 (s : N.State) (i : N.Inputs) :
  R.v47522 (state s) (inputs i) = Zmod.unsigned (N.v47522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47522 s i)) at 1.
  unfold R.v47522, N.v47522.
  rewrite ?node_47520.
  rewrite ?node_47521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47523 (s : N.State) (i : N.Inputs) :
  R.v47523 (state s) (inputs i) = Zmod.unsigned (N.v47523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47523 s i)) at 1.
  unfold R.v47523, N.v47523.
  rewrite ?node_47519.
  rewrite ?node_47522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47524 (s : N.State) (i : N.Inputs) :
  R.v47524 (state s) (inputs i) = Zmod.unsigned (N.v47524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47524 s i)) at 1.
  unfold R.v47524, N.v47524.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47525 (s : N.State) (i : N.Inputs) :
  R.v47525 (state s) (inputs i) = Zmod.unsigned (N.v47525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47525 s i)) at 1.
  unfold R.v47525, N.v47525.
  rewrite ?node_15082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47526 (s : N.State) (i : N.Inputs) :
  R.v47526 (state s) (inputs i) = Zmod.unsigned (N.v47526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47526 s i)) at 1.
  unfold R.v47526, N.v47526.
  unfold R.v6, N.v6.
  rewrite ?node_15078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47527 (s : N.State) (i : N.Inputs) :
  R.v47527 (state s) (inputs i) = Zmod.unsigned (N.v47527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47527 s i)) at 1.
  unfold R.v47527, N.v47527.
  unfold R.v6, N.v6.
  rewrite ?node_15076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47528 (s : N.State) (i : N.Inputs) :
  R.v47528 (state s) (inputs i) = Zmod.unsigned (N.v47528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47528 s i)) at 1.
  unfold R.v47528, N.v47528.
  rewrite ?node_47526.
  rewrite ?node_47527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47529 (s : N.State) (i : N.Inputs) :
  R.v47529 (state s) (inputs i) = Zmod.unsigned (N.v47529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47529 s i)) at 1.
  unfold R.v47529, N.v47529.
  unfold R.v16484, N.v16484.
  rewrite ?node_47528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47530 (s : N.State) (i : N.Inputs) :
  R.v47530 (state s) (inputs i) = Zmod.unsigned (N.v47530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47530 s i)) at 1.
  unfold R.v47530, N.v47530.
  rewrite ?node_47525.
  rewrite ?node_47529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47531 (s : N.State) (i : N.Inputs) :
  R.v47531 (state s) (inputs i) = Zmod.unsigned (N.v47531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47531 s i)) at 1.
  unfold R.v47531, N.v47531.
  unfold R.v6, N.v6.
  rewrite ?node_47530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47532 (s : N.State) (i : N.Inputs) :
  R.v47532 (state s) (inputs i) = Zmod.unsigned (N.v47532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47532 s i)) at 1.
  unfold R.v47532, N.v47532.
  rewrite ?node_15083.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47533 (s : N.State) (i : N.Inputs) :
  R.v47533 (state s) (inputs i) = Zmod.unsigned (N.v47533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47533 s i)) at 1.
  unfold R.v47533, N.v47533.
  unfold R.v6, N.v6.
  rewrite ?node_15177.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47534 (s : N.State) (i : N.Inputs) :
  R.v47534 (state s) (inputs i) = Zmod.unsigned (N.v47534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47534 s i)) at 1.
  unfold R.v47534, N.v47534.
  rewrite ?node_47532.
  rewrite ?node_47533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47535 (s : N.State) (i : N.Inputs) :
  R.v47535 (state s) (inputs i) = Zmod.unsigned (N.v47535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47535 s i)) at 1.
  unfold R.v47535, N.v47535.
  rewrite ?node_47531.
  rewrite ?node_47534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47536 (s : N.State) (i : N.Inputs) :
  R.v47536 (state s) (inputs i) = Zmod.unsigned (N.v47536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47536 s i)) at 1.
  unfold R.v47536, N.v47536.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47537 (s : N.State) (i : N.Inputs) :
  R.v47537 (state s) (inputs i) = Zmod.unsigned (N.v47537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47537 s i)) at 1.
  unfold R.v47537, N.v47537.
  rewrite ?node_15101.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47538 (s : N.State) (i : N.Inputs) :
  R.v47538 (state s) (inputs i) = Zmod.unsigned (N.v47538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47538 s i)) at 1.
  unfold R.v47538, N.v47538.
  rewrite ?node_15097.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47539 (s : N.State) (i : N.Inputs) :
  R.v47539 (state s) (inputs i) = Zmod.unsigned (N.v47539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47539 s i)) at 1.
  unfold R.v47539, N.v47539.
  rewrite ?node_15093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47540 (s : N.State) (i : N.Inputs) :
  R.v47540 (state s) (inputs i) = Zmod.unsigned (N.v47540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47540 s i)) at 1.
  unfold R.v47540, N.v47540.
  unfold R.v6, N.v6.
  rewrite ?node_15089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47541 (s : N.State) (i : N.Inputs) :
  R.v47541 (state s) (inputs i) = Zmod.unsigned (N.v47541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47541 s i)) at 1.
  unfold R.v47541, N.v47541.
  unfold R.v6, N.v6.
  rewrite ?node_15086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47542 (s : N.State) (i : N.Inputs) :
  R.v47542 (state s) (inputs i) = Zmod.unsigned (N.v47542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47542 s i)) at 1.
  unfold R.v47542, N.v47542.
  rewrite ?node_47540.
  rewrite ?node_47541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47543 (s : N.State) (i : N.Inputs) :
  R.v47543 (state s) (inputs i) = Zmod.unsigned (N.v47543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47543 s i)) at 1.
  unfold R.v47543, N.v47543.
  unfold R.v16484, N.v16484.
  rewrite ?node_47542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47544 (s : N.State) (i : N.Inputs) :
  R.v47544 (state s) (inputs i) = Zmod.unsigned (N.v47544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47544 s i)) at 1.
  unfold R.v47544, N.v47544.
  rewrite ?node_47537.
  rewrite ?node_47538.
  rewrite ?node_47539.
  rewrite ?node_47543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47545 (s : N.State) (i : N.Inputs) :
  R.v47545 (state s) (inputs i) = Zmod.unsigned (N.v47545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47545 s i)) at 1.
  unfold R.v47545, N.v47545.
  unfold R.v6, N.v6.
  rewrite ?node_47544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47546 (s : N.State) (i : N.Inputs) :
  R.v47546 (state s) (inputs i) = Zmod.unsigned (N.v47546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47546 s i)) at 1.
  unfold R.v47546, N.v47546.
  rewrite ?node_15102.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47547 (s : N.State) (i : N.Inputs) :
  R.v47547 (state s) (inputs i) = Zmod.unsigned (N.v47547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47547 s i)) at 1.
  unfold R.v47547, N.v47547.
  unfold R.v6, N.v6.
  rewrite ?node_15172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47548 (s : N.State) (i : N.Inputs) :
  R.v47548 (state s) (inputs i) = Zmod.unsigned (N.v47548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47548 s i)) at 1.
  unfold R.v47548, N.v47548.
  unfold R.v6, N.v6.
  rewrite ?node_15181.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47549 (s : N.State) (i : N.Inputs) :
  R.v47549 (state s) (inputs i) = Zmod.unsigned (N.v47549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47549 s i)) at 1.
  unfold R.v47549, N.v47549.
  rewrite ?node_47546.
  rewrite ?node_47547.
  rewrite ?node_47548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47550 (s : N.State) (i : N.Inputs) :
  R.v47550 (state s) (inputs i) = Zmod.unsigned (N.v47550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47550 s i)) at 1.
  unfold R.v47550, N.v47550.
  rewrite ?node_47545.
  rewrite ?node_47549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47551 (s : N.State) (i : N.Inputs) :
  R.v47551 (state s) (inputs i) = Zmod.unsigned (N.v47551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47551 s i)) at 1.
  unfold R.v47551, N.v47551.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47552 (s : N.State) (i : N.Inputs) :
  R.v47552 (state s) (inputs i) = Zmod.unsigned (N.v47552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47552 s i)) at 1.
  unfold R.v47552, N.v47552.
  rewrite ?node_15093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47553 (s : N.State) (i : N.Inputs) :
  R.v47553 (state s) (inputs i) = Zmod.unsigned (N.v47553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47553 s i)) at 1.
  unfold R.v47553, N.v47553.
  unfold R.v6, N.v6.
  rewrite ?node_15089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47554 (s : N.State) (i : N.Inputs) :
  R.v47554 (state s) (inputs i) = Zmod.unsigned (N.v47554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47554 s i)) at 1.
  unfold R.v47554, N.v47554.
  unfold R.v6, N.v6.
  rewrite ?node_15086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47555 (s : N.State) (i : N.Inputs) :
  R.v47555 (state s) (inputs i) = Zmod.unsigned (N.v47555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47555 s i)) at 1.
  unfold R.v47555, N.v47555.
  rewrite ?node_47553.
  rewrite ?node_47554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47556 (s : N.State) (i : N.Inputs) :
  R.v47556 (state s) (inputs i) = Zmod.unsigned (N.v47556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47556 s i)) at 1.
  unfold R.v47556, N.v47556.
  unfold R.v16484, N.v16484.
  rewrite ?node_47555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47557 (s : N.State) (i : N.Inputs) :
  R.v47557 (state s) (inputs i) = Zmod.unsigned (N.v47557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47557 s i)) at 1.
  unfold R.v47557, N.v47557.
  rewrite ?node_47552.
  rewrite ?node_47556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47558 (s : N.State) (i : N.Inputs) :
  R.v47558 (state s) (inputs i) = Zmod.unsigned (N.v47558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47558 s i)) at 1.
  unfold R.v47558, N.v47558.
  unfold R.v6, N.v6.
  rewrite ?node_47557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47559 (s : N.State) (i : N.Inputs) :
  R.v47559 (state s) (inputs i) = Zmod.unsigned (N.v47559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47559 s i)) at 1.
  unfold R.v47559, N.v47559.
  rewrite ?node_15094.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47560 (s : N.State) (i : N.Inputs) :
  R.v47560 (state s) (inputs i) = Zmod.unsigned (N.v47560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47560 s i)) at 1.
  unfold R.v47560, N.v47560.
  unfold R.v6, N.v6.
  rewrite ?node_15172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47561 (s : N.State) (i : N.Inputs) :
  R.v47561 (state s) (inputs i) = Zmod.unsigned (N.v47561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47561 s i)) at 1.
  unfold R.v47561, N.v47561.
  rewrite ?node_47559.
  rewrite ?node_47560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47562 (s : N.State) (i : N.Inputs) :
  R.v47562 (state s) (inputs i) = Zmod.unsigned (N.v47562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47562 s i)) at 1.
  unfold R.v47562, N.v47562.
  rewrite ?node_47558.
  rewrite ?node_47561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47563 (s : N.State) (i : N.Inputs) :
  R.v47563 (state s) (inputs i) = Zmod.unsigned (N.v47563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47563 s i)) at 1.
  unfold R.v47563, N.v47563.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47564 (s : N.State) (i : N.Inputs) :
  R.v47564 (state s) (inputs i) = Zmod.unsigned (N.v47564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47564 s i)) at 1.
  unfold R.v47564, N.v47564.
  rewrite ?node_15101.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47565 (s : N.State) (i : N.Inputs) :
  R.v47565 (state s) (inputs i) = Zmod.unsigned (N.v47565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47565 s i)) at 1.
  unfold R.v47565, N.v47565.
  unfold R.v6, N.v6.
  rewrite ?node_15097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47566 (s : N.State) (i : N.Inputs) :
  R.v47566 (state s) (inputs i) = Zmod.unsigned (N.v47566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47566 s i)) at 1.
  unfold R.v47566, N.v47566.
  unfold R.v6, N.v6.
  rewrite ?node_15094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47567 (s : N.State) (i : N.Inputs) :
  R.v47567 (state s) (inputs i) = Zmod.unsigned (N.v47567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47567 s i)) at 1.
  unfold R.v47567, N.v47567.
  rewrite ?node_47565.
  rewrite ?node_47566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47568 (s : N.State) (i : N.Inputs) :
  R.v47568 (state s) (inputs i) = Zmod.unsigned (N.v47568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47568 s i)) at 1.
  unfold R.v47568, N.v47568.
  unfold R.v16484, N.v16484.
  rewrite ?node_47567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47569 (s : N.State) (i : N.Inputs) :
  R.v47569 (state s) (inputs i) = Zmod.unsigned (N.v47569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47569 s i)) at 1.
  unfold R.v47569, N.v47569.
  rewrite ?node_47564.
  rewrite ?node_47568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47570 (s : N.State) (i : N.Inputs) :
  R.v47570 (state s) (inputs i) = Zmod.unsigned (N.v47570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47570 s i)) at 1.
  unfold R.v47570, N.v47570.
  unfold R.v6, N.v6.
  rewrite ?node_47569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47571 (s : N.State) (i : N.Inputs) :
  R.v47571 (state s) (inputs i) = Zmod.unsigned (N.v47571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47571 s i)) at 1.
  unfold R.v47571, N.v47571.
  rewrite ?node_15102.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47572 (s : N.State) (i : N.Inputs) :
  R.v47572 (state s) (inputs i) = Zmod.unsigned (N.v47572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47572 s i)) at 1.
  unfold R.v47572, N.v47572.
  unfold R.v6, N.v6.
  rewrite ?node_15181.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47573 (s : N.State) (i : N.Inputs) :
  R.v47573 (state s) (inputs i) = Zmod.unsigned (N.v47573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47573 s i)) at 1.
  unfold R.v47573, N.v47573.
  rewrite ?node_47571.
  rewrite ?node_47572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47574 (s : N.State) (i : N.Inputs) :
  R.v47574 (state s) (inputs i) = Zmod.unsigned (N.v47574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47574 s i)) at 1.
  unfold R.v47574, N.v47574.
  rewrite ?node_47570.
  rewrite ?node_47573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47575 (s : N.State) (i : N.Inputs) :
  R.v47575 (state s) (inputs i) = Zmod.unsigned (N.v47575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47575 s i)) at 1.
  unfold R.v47575, N.v47575.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47576 (s : N.State) (i : N.Inputs) :
  R.v47576 (state s) (inputs i) = Zmod.unsigned (N.v47576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47576 s i)) at 1.
  unfold R.v47576, N.v47576.
  rewrite ?node_15153.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47577 (s : N.State) (i : N.Inputs) :
  R.v47577 (state s) (inputs i) = Zmod.unsigned (N.v47577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47577 s i)) at 1.
  unfold R.v47577, N.v47577.
  rewrite ?node_15149.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47578 (s : N.State) (i : N.Inputs) :
  R.v47578 (state s) (inputs i) = Zmod.unsigned (N.v47578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47578 s i)) at 1.
  unfold R.v47578, N.v47578.
  rewrite ?node_15147.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47579 (s : N.State) (i : N.Inputs) :
  R.v47579 (state s) (inputs i) = Zmod.unsigned (N.v47579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47579 s i)) at 1.
  unfold R.v47579, N.v47579.
  unfold R.v6, N.v6.
  rewrite ?node_15139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47580 (s : N.State) (i : N.Inputs) :
  R.v47580 (state s) (inputs i) = Zmod.unsigned (N.v47580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47580 s i)) at 1.
  unfold R.v47580, N.v47580.
  unfold R.v6, N.v6.
  rewrite ?node_15132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47581 (s : N.State) (i : N.Inputs) :
  R.v47581 (state s) (inputs i) = Zmod.unsigned (N.v47581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47581 s i)) at 1.
  unfold R.v47581, N.v47581.
  rewrite ?node_47579.
  rewrite ?node_47580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47582 (s : N.State) (i : N.Inputs) :
  R.v47582 (state s) (inputs i) = Zmod.unsigned (N.v47582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47582 s i)) at 1.
  unfold R.v47582, N.v47582.
  unfold R.v16484, N.v16484.
  rewrite ?node_47581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47583 (s : N.State) (i : N.Inputs) :
  R.v47583 (state s) (inputs i) = Zmod.unsigned (N.v47583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47583 s i)) at 1.
  unfold R.v47583, N.v47583.
  rewrite ?node_47576.
  rewrite ?node_47577.
  rewrite ?node_47578.
  rewrite ?node_47582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47584 (s : N.State) (i : N.Inputs) :
  R.v47584 (state s) (inputs i) = Zmod.unsigned (N.v47584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47584 s i)) at 1.
  unfold R.v47584, N.v47584.
  unfold R.v6, N.v6.
  rewrite ?node_47583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47585 (s : N.State) (i : N.Inputs) :
  R.v47585 (state s) (inputs i) = Zmod.unsigned (N.v47585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47585 s i)) at 1.
  unfold R.v47585, N.v47585.
  rewrite ?node_15154.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47586 (s : N.State) (i : N.Inputs) :
  R.v47586 (state s) (inputs i) = Zmod.unsigned (N.v47586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47586 s i)) at 1.
  unfold R.v47586, N.v47586.
  unfold R.v6, N.v6.
  rewrite ?node_15223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47587 (s : N.State) (i : N.Inputs) :
  R.v47587 (state s) (inputs i) = Zmod.unsigned (N.v47587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47587 s i)) at 1.
  unfold R.v47587, N.v47587.
  unfold R.v6, N.v6.
  rewrite ?node_15245.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47588 (s : N.State) (i : N.Inputs) :
  R.v47588 (state s) (inputs i) = Zmod.unsigned (N.v47588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47588 s i)) at 1.
  unfold R.v47588, N.v47588.
  rewrite ?node_47585.
  rewrite ?node_47586.
  rewrite ?node_47587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47589 (s : N.State) (i : N.Inputs) :
  R.v47589 (state s) (inputs i) = Zmod.unsigned (N.v47589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47589 s i)) at 1.
  unfold R.v47589, N.v47589.
  rewrite ?node_47584.
  rewrite ?node_47588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47590 (s : N.State) (i : N.Inputs) :
  R.v47590 (state s) (inputs i) = Zmod.unsigned (N.v47590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47590 s i)) at 1.
  unfold R.v47590, N.v47590.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47591 (s : N.State) (i : N.Inputs) :
  R.v47591 (state s) (inputs i) = Zmod.unsigned (N.v47591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47591 s i)) at 1.
  unfold R.v47591, N.v47591.
  rewrite ?node_15147.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47592 (s : N.State) (i : N.Inputs) :
  R.v47592 (state s) (inputs i) = Zmod.unsigned (N.v47592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47592 s i)) at 1.
  unfold R.v47592, N.v47592.
  unfold R.v6, N.v6.
  rewrite ?node_15139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47593 (s : N.State) (i : N.Inputs) :
  R.v47593 (state s) (inputs i) = Zmod.unsigned (N.v47593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47593 s i)) at 1.
  unfold R.v47593, N.v47593.
  unfold R.v6, N.v6.
  rewrite ?node_15132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47594 (s : N.State) (i : N.Inputs) :
  R.v47594 (state s) (inputs i) = Zmod.unsigned (N.v47594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47594 s i)) at 1.
  unfold R.v47594, N.v47594.
  rewrite ?node_47592.
  rewrite ?node_47593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47595 (s : N.State) (i : N.Inputs) :
  R.v47595 (state s) (inputs i) = Zmod.unsigned (N.v47595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47595 s i)) at 1.
  unfold R.v47595, N.v47595.
  unfold R.v16484, N.v16484.
  rewrite ?node_47594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47596 (s : N.State) (i : N.Inputs) :
  R.v47596 (state s) (inputs i) = Zmod.unsigned (N.v47596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47596 s i)) at 1.
  unfold R.v47596, N.v47596.
  rewrite ?node_47591.
  rewrite ?node_47595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47597 (s : N.State) (i : N.Inputs) :
  R.v47597 (state s) (inputs i) = Zmod.unsigned (N.v47597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47597 s i)) at 1.
  unfold R.v47597, N.v47597.
  unfold R.v6, N.v6.
  rewrite ?node_47596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47598 (s : N.State) (i : N.Inputs) :
  R.v47598 (state s) (inputs i) = Zmod.unsigned (N.v47598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47598 s i)) at 1.
  unfold R.v47598, N.v47598.
  rewrite ?node_15148.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47599 (s : N.State) (i : N.Inputs) :
  R.v47599 (state s) (inputs i) = Zmod.unsigned (N.v47599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47599 s i)) at 1.
  unfold R.v47599, N.v47599.
  unfold R.v6, N.v6.
  rewrite ?node_15223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47600 (s : N.State) (i : N.Inputs) :
  R.v47600 (state s) (inputs i) = Zmod.unsigned (N.v47600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47600 s i)) at 1.
  unfold R.v47600, N.v47600.
  rewrite ?node_47598.
  rewrite ?node_47599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47601 (s : N.State) (i : N.Inputs) :
  R.v47601 (state s) (inputs i) = Zmod.unsigned (N.v47601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47601 s i)) at 1.
  unfold R.v47601, N.v47601.
  rewrite ?node_47597.
  rewrite ?node_47600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47602 (s : N.State) (i : N.Inputs) :
  R.v47602 (state s) (inputs i) = Zmod.unsigned (N.v47602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47602 s i)) at 1.
  unfold R.v47602, N.v47602.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47603 (s : N.State) (i : N.Inputs) :
  R.v47603 (state s) (inputs i) = Zmod.unsigned (N.v47603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47603 s i)) at 1.
  unfold R.v47603, N.v47603.
  rewrite ?node_15153.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47604 (s : N.State) (i : N.Inputs) :
  R.v47604 (state s) (inputs i) = Zmod.unsigned (N.v47604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47604 s i)) at 1.
  unfold R.v47604, N.v47604.
  unfold R.v6, N.v6.
  rewrite ?node_15149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47605 (s : N.State) (i : N.Inputs) :
  R.v47605 (state s) (inputs i) = Zmod.unsigned (N.v47605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47605 s i)) at 1.
  unfold R.v47605, N.v47605.
  unfold R.v6, N.v6.
  rewrite ?node_15148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47606 (s : N.State) (i : N.Inputs) :
  R.v47606 (state s) (inputs i) = Zmod.unsigned (N.v47606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47606 s i)) at 1.
  unfold R.v47606, N.v47606.
  rewrite ?node_47604.
  rewrite ?node_47605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47607 (s : N.State) (i : N.Inputs) :
  R.v47607 (state s) (inputs i) = Zmod.unsigned (N.v47607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47607 s i)) at 1.
  unfold R.v47607, N.v47607.
  unfold R.v16484, N.v16484.
  rewrite ?node_47606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47608 (s : N.State) (i : N.Inputs) :
  R.v47608 (state s) (inputs i) = Zmod.unsigned (N.v47608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47608 s i)) at 1.
  unfold R.v47608, N.v47608.
  rewrite ?node_47603.
  rewrite ?node_47607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47609 (s : N.State) (i : N.Inputs) :
  R.v47609 (state s) (inputs i) = Zmod.unsigned (N.v47609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47609 s i)) at 1.
  unfold R.v47609, N.v47609.
  unfold R.v6, N.v6.
  rewrite ?node_47608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47610 (s : N.State) (i : N.Inputs) :
  R.v47610 (state s) (inputs i) = Zmod.unsigned (N.v47610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47610 s i)) at 1.
  unfold R.v47610, N.v47610.
  rewrite ?node_15154.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47611 (s : N.State) (i : N.Inputs) :
  R.v47611 (state s) (inputs i) = Zmod.unsigned (N.v47611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47611 s i)) at 1.
  unfold R.v47611, N.v47611.
  unfold R.v6, N.v6.
  rewrite ?node_15245.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47612 (s : N.State) (i : N.Inputs) :
  R.v47612 (state s) (inputs i) = Zmod.unsigned (N.v47612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47612 s i)) at 1.
  unfold R.v47612, N.v47612.
  rewrite ?node_47610.
  rewrite ?node_47611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47613 (s : N.State) (i : N.Inputs) :
  R.v47613 (state s) (inputs i) = Zmod.unsigned (N.v47613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47613 s i)) at 1.
  unfold R.v47613, N.v47613.
  rewrite ?node_47609.
  rewrite ?node_47612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47614 (s : N.State) (i : N.Inputs) :
  R.v47614 (state s) (inputs i) = Zmod.unsigned (N.v47614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47614 s i)) at 1.
  unfold R.v47614, N.v47614.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47615 (s : N.State) (i : N.Inputs) :
  R.v47615 (state s) (inputs i) = Zmod.unsigned (N.v47615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47615 s i)) at 1.
  unfold R.v47615, N.v47615.
  rewrite ?node_15172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47616 (s : N.State) (i : N.Inputs) :
  R.v47616 (state s) (inputs i) = Zmod.unsigned (N.v47616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47616 s i)) at 1.
  unfold R.v47616, N.v47616.
  rewrite ?node_15168.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47617 (s : N.State) (i : N.Inputs) :
  R.v47617 (state s) (inputs i) = Zmod.unsigned (N.v47617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47617 s i)) at 1.
  unfold R.v47617, N.v47617.
  rewrite ?node_15164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47618 (s : N.State) (i : N.Inputs) :
  R.v47618 (state s) (inputs i) = Zmod.unsigned (N.v47618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47618 s i)) at 1.
  unfold R.v47618, N.v47618.
  unfold R.v6, N.v6.
  rewrite ?node_15160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47619 (s : N.State) (i : N.Inputs) :
  R.v47619 (state s) (inputs i) = Zmod.unsigned (N.v47619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47619 s i)) at 1.
  unfold R.v47619, N.v47619.
  unfold R.v6, N.v6.
  rewrite ?node_15157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47620 (s : N.State) (i : N.Inputs) :
  R.v47620 (state s) (inputs i) = Zmod.unsigned (N.v47620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47620 s i)) at 1.
  unfold R.v47620, N.v47620.
  rewrite ?node_47618.
  rewrite ?node_47619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47621 (s : N.State) (i : N.Inputs) :
  R.v47621 (state s) (inputs i) = Zmod.unsigned (N.v47621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47621 s i)) at 1.
  unfold R.v47621, N.v47621.
  unfold R.v16484, N.v16484.
  rewrite ?node_47620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47622 (s : N.State) (i : N.Inputs) :
  R.v47622 (state s) (inputs i) = Zmod.unsigned (N.v47622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47622 s i)) at 1.
  unfold R.v47622, N.v47622.
  rewrite ?node_47615.
  rewrite ?node_47616.
  rewrite ?node_47617.
  rewrite ?node_47621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47623 (s : N.State) (i : N.Inputs) :
  R.v47623 (state s) (inputs i) = Zmod.unsigned (N.v47623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47623 s i)) at 1.
  unfold R.v47623, N.v47623.
  unfold R.v6, N.v6.
  rewrite ?node_47622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47624 (s : N.State) (i : N.Inputs) :
  R.v47624 (state s) (inputs i) = Zmod.unsigned (N.v47624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47624 s i)) at 1.
  unfold R.v47624, N.v47624.
  rewrite ?node_15173.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47625 (s : N.State) (i : N.Inputs) :
  R.v47625 (state s) (inputs i) = Zmod.unsigned (N.v47625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47625 s i)) at 1.
  unfold R.v47625, N.v47625.
  unfold R.v6, N.v6.
  rewrite ?node_15240.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47626 (s : N.State) (i : N.Inputs) :
  R.v47626 (state s) (inputs i) = Zmod.unsigned (N.v47626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47626 s i)) at 1.
  unfold R.v47626, N.v47626.
  unfold R.v6, N.v6.
  rewrite ?node_15249.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47627 (s : N.State) (i : N.Inputs) :
  R.v47627 (state s) (inputs i) = Zmod.unsigned (N.v47627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47627 s i)) at 1.
  unfold R.v47627, N.v47627.
  rewrite ?node_47624.
  rewrite ?node_47625.
  rewrite ?node_47626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47628 (s : N.State) (i : N.Inputs) :
  R.v47628 (state s) (inputs i) = Zmod.unsigned (N.v47628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47628 s i)) at 1.
  unfold R.v47628, N.v47628.
  rewrite ?node_47623.
  rewrite ?node_47627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47629 (s : N.State) (i : N.Inputs) :
  R.v47629 (state s) (inputs i) = Zmod.unsigned (N.v47629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47629 s i)) at 1.
  unfold R.v47629, N.v47629.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47630 (s : N.State) (i : N.Inputs) :
  R.v47630 (state s) (inputs i) = Zmod.unsigned (N.v47630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47630 s i)) at 1.
  unfold R.v47630, N.v47630.
  rewrite ?node_15164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47631 (s : N.State) (i : N.Inputs) :
  R.v47631 (state s) (inputs i) = Zmod.unsigned (N.v47631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47631 s i)) at 1.
  unfold R.v47631, N.v47631.
  unfold R.v6, N.v6.
  rewrite ?node_15160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47632 (s : N.State) (i : N.Inputs) :
  R.v47632 (state s) (inputs i) = Zmod.unsigned (N.v47632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47632 s i)) at 1.
  unfold R.v47632, N.v47632.
  unfold R.v6, N.v6.
  rewrite ?node_15157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47633 (s : N.State) (i : N.Inputs) :
  R.v47633 (state s) (inputs i) = Zmod.unsigned (N.v47633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47633 s i)) at 1.
  unfold R.v47633, N.v47633.
  rewrite ?node_47631.
  rewrite ?node_47632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47634 (s : N.State) (i : N.Inputs) :
  R.v47634 (state s) (inputs i) = Zmod.unsigned (N.v47634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47634 s i)) at 1.
  unfold R.v47634, N.v47634.
  unfold R.v16484, N.v16484.
  rewrite ?node_47633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47635 (s : N.State) (i : N.Inputs) :
  R.v47635 (state s) (inputs i) = Zmod.unsigned (N.v47635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47635 s i)) at 1.
  unfold R.v47635, N.v47635.
  rewrite ?node_47630.
  rewrite ?node_47634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47636 (s : N.State) (i : N.Inputs) :
  R.v47636 (state s) (inputs i) = Zmod.unsigned (N.v47636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47636 s i)) at 1.
  unfold R.v47636, N.v47636.
  unfold R.v6, N.v6.
  rewrite ?node_47635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47637 (s : N.State) (i : N.Inputs) :
  R.v47637 (state s) (inputs i) = Zmod.unsigned (N.v47637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47637 s i)) at 1.
  unfold R.v47637, N.v47637.
  rewrite ?node_15165.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47638 (s : N.State) (i : N.Inputs) :
  R.v47638 (state s) (inputs i) = Zmod.unsigned (N.v47638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47638 s i)) at 1.
  unfold R.v47638, N.v47638.
  unfold R.v6, N.v6.
  rewrite ?node_15240.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47639 (s : N.State) (i : N.Inputs) :
  R.v47639 (state s) (inputs i) = Zmod.unsigned (N.v47639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47639 s i)) at 1.
  unfold R.v47639, N.v47639.
  rewrite ?node_47637.
  rewrite ?node_47638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47640 (s : N.State) (i : N.Inputs) :
  R.v47640 (state s) (inputs i) = Zmod.unsigned (N.v47640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47640 s i)) at 1.
  unfold R.v47640, N.v47640.
  rewrite ?node_47636.
  rewrite ?node_47639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47641 (s : N.State) (i : N.Inputs) :
  R.v47641 (state s) (inputs i) = Zmod.unsigned (N.v47641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47641 s i)) at 1.
  unfold R.v47641, N.v47641.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47642 (s : N.State) (i : N.Inputs) :
  R.v47642 (state s) (inputs i) = Zmod.unsigned (N.v47642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47642 s i)) at 1.
  unfold R.v47642, N.v47642.
  rewrite ?node_15172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47643 (s : N.State) (i : N.Inputs) :
  R.v47643 (state s) (inputs i) = Zmod.unsigned (N.v47643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47643 s i)) at 1.
  unfold R.v47643, N.v47643.
  unfold R.v6, N.v6.
  rewrite ?node_15168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47644 (s : N.State) (i : N.Inputs) :
  R.v47644 (state s) (inputs i) = Zmod.unsigned (N.v47644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47644 s i)) at 1.
  unfold R.v47644, N.v47644.
  unfold R.v6, N.v6.
  rewrite ?node_15165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47645 (s : N.State) (i : N.Inputs) :
  R.v47645 (state s) (inputs i) = Zmod.unsigned (N.v47645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47645 s i)) at 1.
  unfold R.v47645, N.v47645.
  rewrite ?node_47643.
  rewrite ?node_47644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47646 (s : N.State) (i : N.Inputs) :
  R.v47646 (state s) (inputs i) = Zmod.unsigned (N.v47646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47646 s i)) at 1.
  unfold R.v47646, N.v47646.
  unfold R.v16484, N.v16484.
  rewrite ?node_47645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47647 (s : N.State) (i : N.Inputs) :
  R.v47647 (state s) (inputs i) = Zmod.unsigned (N.v47647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47647 s i)) at 1.
  unfold R.v47647, N.v47647.
  rewrite ?node_47642.
  rewrite ?node_47646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47648 (s : N.State) (i : N.Inputs) :
  R.v47648 (state s) (inputs i) = Zmod.unsigned (N.v47648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47648 s i)) at 1.
  unfold R.v47648, N.v47648.
  unfold R.v6, N.v6.
  rewrite ?node_47647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47649 (s : N.State) (i : N.Inputs) :
  R.v47649 (state s) (inputs i) = Zmod.unsigned (N.v47649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47649 s i)) at 1.
  unfold R.v47649, N.v47649.
  rewrite ?node_15173.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47650 (s : N.State) (i : N.Inputs) :
  R.v47650 (state s) (inputs i) = Zmod.unsigned (N.v47650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47650 s i)) at 1.
  unfold R.v47650, N.v47650.
  unfold R.v6, N.v6.
  rewrite ?node_15249.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47651 (s : N.State) (i : N.Inputs) :
  R.v47651 (state s) (inputs i) = Zmod.unsigned (N.v47651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47651 s i)) at 1.
  unfold R.v47651, N.v47651.
  rewrite ?node_47649.
  rewrite ?node_47650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47652 (s : N.State) (i : N.Inputs) :
  R.v47652 (state s) (inputs i) = Zmod.unsigned (N.v47652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47652 s i)) at 1.
  unfold R.v47652, N.v47652.
  rewrite ?node_47648.
  rewrite ?node_47651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47653 (s : N.State) (i : N.Inputs) :
  R.v47653 (state s) (inputs i) = Zmod.unsigned (N.v47653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47653 s i)) at 1.
  unfold R.v47653, N.v47653.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47654 (s : N.State) (i : N.Inputs) :
  R.v47654 (state s) (inputs i) = Zmod.unsigned (N.v47654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47654 s i)) at 1.
  unfold R.v47654, N.v47654.
  rewrite ?node_15223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47655 (s : N.State) (i : N.Inputs) :
  R.v47655 (state s) (inputs i) = Zmod.unsigned (N.v47655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47655 s i)) at 1.
  unfold R.v47655, N.v47655.
  rewrite ?node_15219.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47656 (s : N.State) (i : N.Inputs) :
  R.v47656 (state s) (inputs i) = Zmod.unsigned (N.v47656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47656 s i)) at 1.
  unfold R.v47656, N.v47656.
  rewrite ?node_15217.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47657 (s : N.State) (i : N.Inputs) :
  R.v47657 (state s) (inputs i) = Zmod.unsigned (N.v47657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47657 s i)) at 1.
  unfold R.v47657, N.v47657.
  unfold R.v6, N.v6.
  rewrite ?node_15209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47658 (s : N.State) (i : N.Inputs) :
  R.v47658 (state s) (inputs i) = Zmod.unsigned (N.v47658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47658 s i)) at 1.
  unfold R.v47658, N.v47658.
  unfold R.v6, N.v6.
  rewrite ?node_15202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47659 (s : N.State) (i : N.Inputs) :
  R.v47659 (state s) (inputs i) = Zmod.unsigned (N.v47659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47659 s i)) at 1.
  unfold R.v47659, N.v47659.
  rewrite ?node_47657.
  rewrite ?node_47658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47660 (s : N.State) (i : N.Inputs) :
  R.v47660 (state s) (inputs i) = Zmod.unsigned (N.v47660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47660 s i)) at 1.
  unfold R.v47660, N.v47660.
  unfold R.v16484, N.v16484.
  rewrite ?node_47659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47661 (s : N.State) (i : N.Inputs) :
  R.v47661 (state s) (inputs i) = Zmod.unsigned (N.v47661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47661 s i)) at 1.
  unfold R.v47661, N.v47661.
  rewrite ?node_47654.
  rewrite ?node_47655.
  rewrite ?node_47656.
  rewrite ?node_47660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47662 (s : N.State) (i : N.Inputs) :
  R.v47662 (state s) (inputs i) = Zmod.unsigned (N.v47662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47662 s i)) at 1.
  unfold R.v47662, N.v47662.
  unfold R.v6, N.v6.
  rewrite ?node_47661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47663 (s : N.State) (i : N.Inputs) :
  R.v47663 (state s) (inputs i) = Zmod.unsigned (N.v47663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47663 s i)) at 1.
  unfold R.v47663, N.v47663.
  rewrite ?node_15224.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47664 (s : N.State) (i : N.Inputs) :
  R.v47664 (state s) (inputs i) = Zmod.unsigned (N.v47664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47664 s i)) at 1.
  unfold R.v47664, N.v47664.
  unfold R.v6, N.v6.
  rewrite ?node_15289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47665 (s : N.State) (i : N.Inputs) :
  R.v47665 (state s) (inputs i) = Zmod.unsigned (N.v47665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47665 s i)) at 1.
  unfold R.v47665, N.v47665.
  unfold R.v6, N.v6.
  rewrite ?node_15311.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47666 (s : N.State) (i : N.Inputs) :
  R.v47666 (state s) (inputs i) = Zmod.unsigned (N.v47666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47666 s i)) at 1.
  unfold R.v47666, N.v47666.
  rewrite ?node_47663.
  rewrite ?node_47664.
  rewrite ?node_47665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47667 (s : N.State) (i : N.Inputs) :
  R.v47667 (state s) (inputs i) = Zmod.unsigned (N.v47667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47667 s i)) at 1.
  unfold R.v47667, N.v47667.
  rewrite ?node_47662.
  rewrite ?node_47666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47668 (s : N.State) (i : N.Inputs) :
  R.v47668 (state s) (inputs i) = Zmod.unsigned (N.v47668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47668 s i)) at 1.
  unfold R.v47668, N.v47668.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47669 (s : N.State) (i : N.Inputs) :
  R.v47669 (state s) (inputs i) = Zmod.unsigned (N.v47669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47669 s i)) at 1.
  unfold R.v47669, N.v47669.
  rewrite ?node_15217.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47670 (s : N.State) (i : N.Inputs) :
  R.v47670 (state s) (inputs i) = Zmod.unsigned (N.v47670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47670 s i)) at 1.
  unfold R.v47670, N.v47670.
  unfold R.v6, N.v6.
  rewrite ?node_15209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47671 (s : N.State) (i : N.Inputs) :
  R.v47671 (state s) (inputs i) = Zmod.unsigned (N.v47671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47671 s i)) at 1.
  unfold R.v47671, N.v47671.
  unfold R.v6, N.v6.
  rewrite ?node_15202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47672 (s : N.State) (i : N.Inputs) :
  R.v47672 (state s) (inputs i) = Zmod.unsigned (N.v47672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47672 s i)) at 1.
  unfold R.v47672, N.v47672.
  rewrite ?node_47670.
  rewrite ?node_47671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47673 (s : N.State) (i : N.Inputs) :
  R.v47673 (state s) (inputs i) = Zmod.unsigned (N.v47673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47673 s i)) at 1.
  unfold R.v47673, N.v47673.
  unfold R.v16484, N.v16484.
  rewrite ?node_47672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47674 (s : N.State) (i : N.Inputs) :
  R.v47674 (state s) (inputs i) = Zmod.unsigned (N.v47674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47674 s i)) at 1.
  unfold R.v47674, N.v47674.
  rewrite ?node_47669.
  rewrite ?node_47673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47675 (s : N.State) (i : N.Inputs) :
  R.v47675 (state s) (inputs i) = Zmod.unsigned (N.v47675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47675 s i)) at 1.
  unfold R.v47675, N.v47675.
  unfold R.v6, N.v6.
  rewrite ?node_47674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47676 (s : N.State) (i : N.Inputs) :
  R.v47676 (state s) (inputs i) = Zmod.unsigned (N.v47676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47676 s i)) at 1.
  unfold R.v47676, N.v47676.
  rewrite ?node_15218.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47677 (s : N.State) (i : N.Inputs) :
  R.v47677 (state s) (inputs i) = Zmod.unsigned (N.v47677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47677 s i)) at 1.
  unfold R.v47677, N.v47677.
  unfold R.v6, N.v6.
  rewrite ?node_15289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47678 (s : N.State) (i : N.Inputs) :
  R.v47678 (state s) (inputs i) = Zmod.unsigned (N.v47678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47678 s i)) at 1.
  unfold R.v47678, N.v47678.
  rewrite ?node_47676.
  rewrite ?node_47677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47679 (s : N.State) (i : N.Inputs) :
  R.v47679 (state s) (inputs i) = Zmod.unsigned (N.v47679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47679 s i)) at 1.
  unfold R.v47679, N.v47679.
  rewrite ?node_47675.
  rewrite ?node_47678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47680 (s : N.State) (i : N.Inputs) :
  R.v47680 (state s) (inputs i) = Zmod.unsigned (N.v47680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47680 s i)) at 1.
  unfold R.v47680, N.v47680.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47681 (s : N.State) (i : N.Inputs) :
  R.v47681 (state s) (inputs i) = Zmod.unsigned (N.v47681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47681 s i)) at 1.
  unfold R.v47681, N.v47681.
  rewrite ?node_15223.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47682 (s : N.State) (i : N.Inputs) :
  R.v47682 (state s) (inputs i) = Zmod.unsigned (N.v47682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47682 s i)) at 1.
  unfold R.v47682, N.v47682.
  unfold R.v6, N.v6.
  rewrite ?node_15219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47683 (s : N.State) (i : N.Inputs) :
  R.v47683 (state s) (inputs i) = Zmod.unsigned (N.v47683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47683 s i)) at 1.
  unfold R.v47683, N.v47683.
  unfold R.v6, N.v6.
  rewrite ?node_15218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47684 (s : N.State) (i : N.Inputs) :
  R.v47684 (state s) (inputs i) = Zmod.unsigned (N.v47684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47684 s i)) at 1.
  unfold R.v47684, N.v47684.
  rewrite ?node_47682.
  rewrite ?node_47683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47685 (s : N.State) (i : N.Inputs) :
  R.v47685 (state s) (inputs i) = Zmod.unsigned (N.v47685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47685 s i)) at 1.
  unfold R.v47685, N.v47685.
  unfold R.v16484, N.v16484.
  rewrite ?node_47684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47686 (s : N.State) (i : N.Inputs) :
  R.v47686 (state s) (inputs i) = Zmod.unsigned (N.v47686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47686 s i)) at 1.
  unfold R.v47686, N.v47686.
  rewrite ?node_47681.
  rewrite ?node_47685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47687 (s : N.State) (i : N.Inputs) :
  R.v47687 (state s) (inputs i) = Zmod.unsigned (N.v47687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47687 s i)) at 1.
  unfold R.v47687, N.v47687.
  unfold R.v6, N.v6.
  rewrite ?node_47686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47688 (s : N.State) (i : N.Inputs) :
  R.v47688 (state s) (inputs i) = Zmod.unsigned (N.v47688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47688 s i)) at 1.
  unfold R.v47688, N.v47688.
  rewrite ?node_15224.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47689 (s : N.State) (i : N.Inputs) :
  R.v47689 (state s) (inputs i) = Zmod.unsigned (N.v47689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47689 s i)) at 1.
  unfold R.v47689, N.v47689.
  unfold R.v6, N.v6.
  rewrite ?node_15311.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47690 (s : N.State) (i : N.Inputs) :
  R.v47690 (state s) (inputs i) = Zmod.unsigned (N.v47690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47690 s i)) at 1.
  unfold R.v47690, N.v47690.
  rewrite ?node_47688.
  rewrite ?node_47689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47691 (s : N.State) (i : N.Inputs) :
  R.v47691 (state s) (inputs i) = Zmod.unsigned (N.v47691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47691 s i)) at 1.
  unfold R.v47691, N.v47691.
  rewrite ?node_47687.
  rewrite ?node_47690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47692 (s : N.State) (i : N.Inputs) :
  R.v47692 (state s) (inputs i) = Zmod.unsigned (N.v47692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47692 s i)) at 1.
  unfold R.v47692, N.v47692.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47693 (s : N.State) (i : N.Inputs) :
  R.v47693 (state s) (inputs i) = Zmod.unsigned (N.v47693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47693 s i)) at 1.
  unfold R.v47693, N.v47693.
  rewrite ?node_15240.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47694 (s : N.State) (i : N.Inputs) :
  R.v47694 (state s) (inputs i) = Zmod.unsigned (N.v47694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47694 s i)) at 1.
  unfold R.v47694, N.v47694.
  rewrite ?node_15236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47695 (s : N.State) (i : N.Inputs) :
  R.v47695 (state s) (inputs i) = Zmod.unsigned (N.v47695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47695 s i)) at 1.
  unfold R.v47695, N.v47695.
  rewrite ?node_15234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47696 (s : N.State) (i : N.Inputs) :
  R.v47696 (state s) (inputs i) = Zmod.unsigned (N.v47696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47696 s i)) at 1.
  unfold R.v47696, N.v47696.
  unfold R.v6, N.v6.
  rewrite ?node_15230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47697 (s : N.State) (i : N.Inputs) :
  R.v47697 (state s) (inputs i) = Zmod.unsigned (N.v47697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47697 s i)) at 1.
  unfold R.v47697, N.v47697.
  unfold R.v6, N.v6.
  rewrite ?node_15227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47698 (s : N.State) (i : N.Inputs) :
  R.v47698 (state s) (inputs i) = Zmod.unsigned (N.v47698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47698 s i)) at 1.
  unfold R.v47698, N.v47698.
  rewrite ?node_47696.
  rewrite ?node_47697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47699 (s : N.State) (i : N.Inputs) :
  R.v47699 (state s) (inputs i) = Zmod.unsigned (N.v47699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47699 s i)) at 1.
  unfold R.v47699, N.v47699.
  unfold R.v16484, N.v16484.
  rewrite ?node_47698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47700 (s : N.State) (i : N.Inputs) :
  R.v47700 (state s) (inputs i) = Zmod.unsigned (N.v47700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47700 s i)) at 1.
  unfold R.v47700, N.v47700.
  rewrite ?node_47693.
  rewrite ?node_47694.
  rewrite ?node_47695.
  rewrite ?node_47699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47701 (s : N.State) (i : N.Inputs) :
  R.v47701 (state s) (inputs i) = Zmod.unsigned (N.v47701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47701 s i)) at 1.
  unfold R.v47701, N.v47701.
  unfold R.v6, N.v6.
  rewrite ?node_47700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47702 (s : N.State) (i : N.Inputs) :
  R.v47702 (state s) (inputs i) = Zmod.unsigned (N.v47702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47702 s i)) at 1.
  unfold R.v47702, N.v47702.
  rewrite ?node_15241.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47703 (s : N.State) (i : N.Inputs) :
  R.v47703 (state s) (inputs i) = Zmod.unsigned (N.v47703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47703 s i)) at 1.
  unfold R.v47703, N.v47703.
  unfold R.v6, N.v6.
  rewrite ?node_15306.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47704 (s : N.State) (i : N.Inputs) :
  R.v47704 (state s) (inputs i) = Zmod.unsigned (N.v47704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47704 s i)) at 1.
  unfold R.v47704, N.v47704.
  unfold R.v6, N.v6.
  rewrite ?node_15315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47705 (s : N.State) (i : N.Inputs) :
  R.v47705 (state s) (inputs i) = Zmod.unsigned (N.v47705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47705 s i)) at 1.
  unfold R.v47705, N.v47705.
  rewrite ?node_47702.
  rewrite ?node_47703.
  rewrite ?node_47704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47706 (s : N.State) (i : N.Inputs) :
  R.v47706 (state s) (inputs i) = Zmod.unsigned (N.v47706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47706 s i)) at 1.
  unfold R.v47706, N.v47706.
  rewrite ?node_47701.
  rewrite ?node_47705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47707 (s : N.State) (i : N.Inputs) :
  R.v47707 (state s) (inputs i) = Zmod.unsigned (N.v47707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47707 s i)) at 1.
  unfold R.v47707, N.v47707.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47708 (s : N.State) (i : N.Inputs) :
  R.v47708 (state s) (inputs i) = Zmod.unsigned (N.v47708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47708 s i)) at 1.
  unfold R.v47708, N.v47708.
  rewrite ?node_15234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47709 (s : N.State) (i : N.Inputs) :
  R.v47709 (state s) (inputs i) = Zmod.unsigned (N.v47709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47709 s i)) at 1.
  unfold R.v47709, N.v47709.
  unfold R.v6, N.v6.
  rewrite ?node_15230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47710 (s : N.State) (i : N.Inputs) :
  R.v47710 (state s) (inputs i) = Zmod.unsigned (N.v47710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47710 s i)) at 1.
  unfold R.v47710, N.v47710.
  unfold R.v6, N.v6.
  rewrite ?node_15227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47711 (s : N.State) (i : N.Inputs) :
  R.v47711 (state s) (inputs i) = Zmod.unsigned (N.v47711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47711 s i)) at 1.
  unfold R.v47711, N.v47711.
  rewrite ?node_47709.
  rewrite ?node_47710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47712 (s : N.State) (i : N.Inputs) :
  R.v47712 (state s) (inputs i) = Zmod.unsigned (N.v47712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47712 s i)) at 1.
  unfold R.v47712, N.v47712.
  unfold R.v16484, N.v16484.
  rewrite ?node_47711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47713 (s : N.State) (i : N.Inputs) :
  R.v47713 (state s) (inputs i) = Zmod.unsigned (N.v47713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47713 s i)) at 1.
  unfold R.v47713, N.v47713.
  rewrite ?node_47708.
  rewrite ?node_47712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47714 (s : N.State) (i : N.Inputs) :
  R.v47714 (state s) (inputs i) = Zmod.unsigned (N.v47714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47714 s i)) at 1.
  unfold R.v47714, N.v47714.
  unfold R.v6, N.v6.
  rewrite ?node_47713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47715 (s : N.State) (i : N.Inputs) :
  R.v47715 (state s) (inputs i) = Zmod.unsigned (N.v47715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47715 s i)) at 1.
  unfold R.v47715, N.v47715.
  rewrite ?node_15235.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47716 (s : N.State) (i : N.Inputs) :
  R.v47716 (state s) (inputs i) = Zmod.unsigned (N.v47716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47716 s i)) at 1.
  unfold R.v47716, N.v47716.
  unfold R.v6, N.v6.
  rewrite ?node_15306.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47717 (s : N.State) (i : N.Inputs) :
  R.v47717 (state s) (inputs i) = Zmod.unsigned (N.v47717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47717 s i)) at 1.
  unfold R.v47717, N.v47717.
  rewrite ?node_47715.
  rewrite ?node_47716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47718 (s : N.State) (i : N.Inputs) :
  R.v47718 (state s) (inputs i) = Zmod.unsigned (N.v47718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47718 s i)) at 1.
  unfold R.v47718, N.v47718.
  rewrite ?node_47714.
  rewrite ?node_47717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47719 (s : N.State) (i : N.Inputs) :
  R.v47719 (state s) (inputs i) = Zmod.unsigned (N.v47719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47719 s i)) at 1.
  unfold R.v47719, N.v47719.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47720 (s : N.State) (i : N.Inputs) :
  R.v47720 (state s) (inputs i) = Zmod.unsigned (N.v47720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47720 s i)) at 1.
  unfold R.v47720, N.v47720.
  rewrite ?node_15240.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47721 (s : N.State) (i : N.Inputs) :
  R.v47721 (state s) (inputs i) = Zmod.unsigned (N.v47721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47721 s i)) at 1.
  unfold R.v47721, N.v47721.
  unfold R.v6, N.v6.
  rewrite ?node_15236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47722 (s : N.State) (i : N.Inputs) :
  R.v47722 (state s) (inputs i) = Zmod.unsigned (N.v47722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47722 s i)) at 1.
  unfold R.v47722, N.v47722.
  unfold R.v6, N.v6.
  rewrite ?node_15235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47723 (s : N.State) (i : N.Inputs) :
  R.v47723 (state s) (inputs i) = Zmod.unsigned (N.v47723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47723 s i)) at 1.
  unfold R.v47723, N.v47723.
  rewrite ?node_47721.
  rewrite ?node_47722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47724 (s : N.State) (i : N.Inputs) :
  R.v47724 (state s) (inputs i) = Zmod.unsigned (N.v47724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47724 s i)) at 1.
  unfold R.v47724, N.v47724.
  unfold R.v16484, N.v16484.
  rewrite ?node_47723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47725 (s : N.State) (i : N.Inputs) :
  R.v47725 (state s) (inputs i) = Zmod.unsigned (N.v47725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47725 s i)) at 1.
  unfold R.v47725, N.v47725.
  rewrite ?node_47720.
  rewrite ?node_47724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47726 (s : N.State) (i : N.Inputs) :
  R.v47726 (state s) (inputs i) = Zmod.unsigned (N.v47726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47726 s i)) at 1.
  unfold R.v47726, N.v47726.
  unfold R.v6, N.v6.
  rewrite ?node_47725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47727 (s : N.State) (i : N.Inputs) :
  R.v47727 (state s) (inputs i) = Zmod.unsigned (N.v47727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47727 s i)) at 1.
  unfold R.v47727, N.v47727.
  rewrite ?node_15241.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47728 (s : N.State) (i : N.Inputs) :
  R.v47728 (state s) (inputs i) = Zmod.unsigned (N.v47728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47728 s i)) at 1.
  unfold R.v47728, N.v47728.
  unfold R.v6, N.v6.
  rewrite ?node_15315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47729 (s : N.State) (i : N.Inputs) :
  R.v47729 (state s) (inputs i) = Zmod.unsigned (N.v47729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47729 s i)) at 1.
  unfold R.v47729, N.v47729.
  rewrite ?node_47727.
  rewrite ?node_47728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47730 (s : N.State) (i : N.Inputs) :
  R.v47730 (state s) (inputs i) = Zmod.unsigned (N.v47730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47730 s i)) at 1.
  unfold R.v47730, N.v47730.
  rewrite ?node_47726.
  rewrite ?node_47729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47731 (s : N.State) (i : N.Inputs) :
  R.v47731 (state s) (inputs i) = Zmod.unsigned (N.v47731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47731 s i)) at 1.
  unfold R.v47731, N.v47731.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47732 (s : N.State) (i : N.Inputs) :
  R.v47732 (state s) (inputs i) = Zmod.unsigned (N.v47732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47732 s i)) at 1.
  unfold R.v47732, N.v47732.
  rewrite ?node_15289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47733 (s : N.State) (i : N.Inputs) :
  R.v47733 (state s) (inputs i) = Zmod.unsigned (N.v47733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47733 s i)) at 1.
  unfold R.v47733, N.v47733.
  unfold R.v16463, N.v16463.
  rewrite !state_r2122_nr_5F2141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2122_nr_5F2141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47734 (s : N.State) (i : N.Inputs) :
  R.v47734 (state s) (inputs i) = Zmod.unsigned (N.v47734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47734 s i)) at 1.
  unfold R.v47734, N.v47734.
  rewrite ?node_15284.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47735 (s : N.State) (i : N.Inputs) :
  R.v47735 (state s) (inputs i) = Zmod.unsigned (N.v47735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47735 s i)) at 1.
  unfold R.v47735, N.v47735.
  unfold R.v6, N.v6.
  rewrite ?node_15276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47736 (s : N.State) (i : N.Inputs) :
  R.v47736 (state s) (inputs i) = Zmod.unsigned (N.v47736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47736 s i)) at 1.
  unfold R.v47736, N.v47736.
  unfold R.v6, N.v6.
  rewrite ?node_15269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47737 (s : N.State) (i : N.Inputs) :
  R.v47737 (state s) (inputs i) = Zmod.unsigned (N.v47737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47737 s i)) at 1.
  unfold R.v47737, N.v47737.
  rewrite ?node_47735.
  rewrite ?node_47736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47738 (s : N.State) (i : N.Inputs) :
  R.v47738 (state s) (inputs i) = Zmod.unsigned (N.v47738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47738 s i)) at 1.
  unfold R.v47738, N.v47738.
  unfold R.v16484, N.v16484.
  rewrite ?node_47737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47739 (s : N.State) (i : N.Inputs) :
  R.v47739 (state s) (inputs i) = Zmod.unsigned (N.v47739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47739 s i)) at 1.
  unfold R.v47739, N.v47739.
  rewrite ?node_47732.
  rewrite ?node_47733.
  rewrite ?node_47734.
  rewrite ?node_47738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47740 (s : N.State) (i : N.Inputs) :
  R.v47740 (state s) (inputs i) = Zmod.unsigned (N.v47740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47740 s i)) at 1.
  unfold R.v47740, N.v47740.
  unfold R.v6, N.v6.
  rewrite ?node_47739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47741 (s : N.State) (i : N.Inputs) :
  R.v47741 (state s) (inputs i) = Zmod.unsigned (N.v47741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47741 s i)) at 1.
  unfold R.v47741, N.v47741.
  rewrite ?node_15290.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47742 (s : N.State) (i : N.Inputs) :
  R.v47742 (state s) (inputs i) = Zmod.unsigned (N.v47742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47742 s i)) at 1.
  unfold R.v47742, N.v47742.
  unfold R.v6, N.v6.
  rewrite ?node_15356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47743 (s : N.State) (i : N.Inputs) :
  R.v47743 (state s) (inputs i) = Zmod.unsigned (N.v47743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47743 s i)) at 1.
  unfold R.v47743, N.v47743.
  unfold R.v6, N.v6.
  rewrite ?node_15376.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47744 (s : N.State) (i : N.Inputs) :
  R.v47744 (state s) (inputs i) = Zmod.unsigned (N.v47744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47744 s i)) at 1.
  unfold R.v47744, N.v47744.
  rewrite ?node_47741.
  rewrite ?node_47742.
  rewrite ?node_47743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47745 (s : N.State) (i : N.Inputs) :
  R.v47745 (state s) (inputs i) = Zmod.unsigned (N.v47745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47745 s i)) at 1.
  unfold R.v47745, N.v47745.
  rewrite ?node_47740.
  rewrite ?node_47744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47746 (s : N.State) (i : N.Inputs) :
  R.v47746 (state s) (inputs i) = Zmod.unsigned (N.v47746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47746 s i)) at 1.
  unfold R.v47746, N.v47746.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47747 (s : N.State) (i : N.Inputs) :
  R.v47747 (state s) (inputs i) = Zmod.unsigned (N.v47747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47747 s i)) at 1.
  unfold R.v47747, N.v47747.
  rewrite ?node_15284.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47748 (s : N.State) (i : N.Inputs) :
  R.v47748 (state s) (inputs i) = Zmod.unsigned (N.v47748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47748 s i)) at 1.
  unfold R.v47748, N.v47748.
  unfold R.v6, N.v6.
  rewrite ?node_15276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47749 (s : N.State) (i : N.Inputs) :
  R.v47749 (state s) (inputs i) = Zmod.unsigned (N.v47749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47749 s i)) at 1.
  unfold R.v47749, N.v47749.
  unfold R.v6, N.v6.
  rewrite ?node_15269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47750 (s : N.State) (i : N.Inputs) :
  R.v47750 (state s) (inputs i) = Zmod.unsigned (N.v47750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47750 s i)) at 1.
  unfold R.v47750, N.v47750.
  rewrite ?node_47748.
  rewrite ?node_47749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47751 (s : N.State) (i : N.Inputs) :
  R.v47751 (state s) (inputs i) = Zmod.unsigned (N.v47751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47751 s i)) at 1.
  unfold R.v47751, N.v47751.
  unfold R.v16484, N.v16484.
  rewrite ?node_47750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47752 (s : N.State) (i : N.Inputs) :
  R.v47752 (state s) (inputs i) = Zmod.unsigned (N.v47752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47752 s i)) at 1.
  unfold R.v47752, N.v47752.
  rewrite ?node_47747.
  rewrite ?node_47751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47753 (s : N.State) (i : N.Inputs) :
  R.v47753 (state s) (inputs i) = Zmod.unsigned (N.v47753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47753 s i)) at 1.
  unfold R.v47753, N.v47753.
  unfold R.v6, N.v6.
  rewrite ?node_47752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47754 (s : N.State) (i : N.Inputs) :
  R.v47754 (state s) (inputs i) = Zmod.unsigned (N.v47754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47754 s i)) at 1.
  unfold R.v47754, N.v47754.
  rewrite ?node_15285.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47755 (s : N.State) (i : N.Inputs) :
  R.v47755 (state s) (inputs i) = Zmod.unsigned (N.v47755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47755 s i)) at 1.
  unfold R.v47755, N.v47755.
  unfold R.v6, N.v6.
  rewrite ?node_15356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47756 (s : N.State) (i : N.Inputs) :
  R.v47756 (state s) (inputs i) = Zmod.unsigned (N.v47756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47756 s i)) at 1.
  unfold R.v47756, N.v47756.
  rewrite ?node_47754.
  rewrite ?node_47755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47757 (s : N.State) (i : N.Inputs) :
  R.v47757 (state s) (inputs i) = Zmod.unsigned (N.v47757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47757 s i)) at 1.
  unfold R.v47757, N.v47757.
  rewrite ?node_47753.
  rewrite ?node_47756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47758 (s : N.State) (i : N.Inputs) :
  R.v47758 (state s) (inputs i) = Zmod.unsigned (N.v47758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47758 s i)) at 1.
  unfold R.v47758, N.v47758.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47759 (s : N.State) (i : N.Inputs) :
  R.v47759 (state s) (inputs i) = Zmod.unsigned (N.v47759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47759 s i)) at 1.
  unfold R.v47759, N.v47759.
  rewrite ?node_15289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47760 (s : N.State) (i : N.Inputs) :
  R.v47760 (state s) (inputs i) = Zmod.unsigned (N.v47760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47760 s i)) at 1.
  unfold R.v47760, N.v47760.
  unfold R.v6, N.v6.
  rewrite !state_r2122_nr_5F2141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2122_nr_5F2141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47761 (s : N.State) (i : N.Inputs) :
  R.v47761 (state s) (inputs i) = Zmod.unsigned (N.v47761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47761 s i)) at 1.
  unfold R.v47761, N.v47761.
  unfold R.v6, N.v6.
  rewrite ?node_15285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47762 (s : N.State) (i : N.Inputs) :
  R.v47762 (state s) (inputs i) = Zmod.unsigned (N.v47762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47762 s i)) at 1.
  unfold R.v47762, N.v47762.
  rewrite ?node_47760.
  rewrite ?node_47761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47763 (s : N.State) (i : N.Inputs) :
  R.v47763 (state s) (inputs i) = Zmod.unsigned (N.v47763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47763 s i)) at 1.
  unfold R.v47763, N.v47763.
  unfold R.v16484, N.v16484.
  rewrite ?node_47762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47764 (s : N.State) (i : N.Inputs) :
  R.v47764 (state s) (inputs i) = Zmod.unsigned (N.v47764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47764 s i)) at 1.
  unfold R.v47764, N.v47764.
  rewrite ?node_47759.
  rewrite ?node_47763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47765 (s : N.State) (i : N.Inputs) :
  R.v47765 (state s) (inputs i) = Zmod.unsigned (N.v47765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47765 s i)) at 1.
  unfold R.v47765, N.v47765.
  unfold R.v6, N.v6.
  rewrite ?node_47764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47766 (s : N.State) (i : N.Inputs) :
  R.v47766 (state s) (inputs i) = Zmod.unsigned (N.v47766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47766 s i)) at 1.
  unfold R.v47766, N.v47766.
  rewrite ?node_15290.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47767 (s : N.State) (i : N.Inputs) :
  R.v47767 (state s) (inputs i) = Zmod.unsigned (N.v47767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47767 s i)) at 1.
  unfold R.v47767, N.v47767.
  unfold R.v6, N.v6.
  rewrite ?node_15376.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47768 (s : N.State) (i : N.Inputs) :
  R.v47768 (state s) (inputs i) = Zmod.unsigned (N.v47768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47768 s i)) at 1.
  unfold R.v47768, N.v47768.
  rewrite ?node_47766.
  rewrite ?node_47767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47769 (s : N.State) (i : N.Inputs) :
  R.v47769 (state s) (inputs i) = Zmod.unsigned (N.v47769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47769 s i)) at 1.
  unfold R.v47769, N.v47769.
  rewrite ?node_47765.
  rewrite ?node_47768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47770 (s : N.State) (i : N.Inputs) :
  R.v47770 (state s) (inputs i) = Zmod.unsigned (N.v47770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47770 s i)) at 1.
  unfold R.v47770, N.v47770.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47771 (s : N.State) (i : N.Inputs) :
  R.v47771 (state s) (inputs i) = Zmod.unsigned (N.v47771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47771 s i)) at 1.
  unfold R.v47771, N.v47771.
  rewrite ?node_15306.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47772 (s : N.State) (i : N.Inputs) :
  R.v47772 (state s) (inputs i) = Zmod.unsigned (N.v47772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47772 s i)) at 1.
  unfold R.v47772, N.v47772.
  rewrite ?node_15302.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47773 (s : N.State) (i : N.Inputs) :
  R.v47773 (state s) (inputs i) = Zmod.unsigned (N.v47773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47773 s i)) at 1.
  unfold R.v47773, N.v47773.
  rewrite ?node_15300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47774 (s : N.State) (i : N.Inputs) :
  R.v47774 (state s) (inputs i) = Zmod.unsigned (N.v47774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47774 s i)) at 1.
  unfold R.v47774, N.v47774.
  unfold R.v6, N.v6.
  rewrite ?node_15296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47775 (s : N.State) (i : N.Inputs) :
  R.v47775 (state s) (inputs i) = Zmod.unsigned (N.v47775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47775 s i)) at 1.
  unfold R.v47775, N.v47775.
  unfold R.v6, N.v6.
  rewrite ?node_15293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47776 (s : N.State) (i : N.Inputs) :
  R.v47776 (state s) (inputs i) = Zmod.unsigned (N.v47776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47776 s i)) at 1.
  unfold R.v47776, N.v47776.
  rewrite ?node_47774.
  rewrite ?node_47775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47777 (s : N.State) (i : N.Inputs) :
  R.v47777 (state s) (inputs i) = Zmod.unsigned (N.v47777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47777 s i)) at 1.
  unfold R.v47777, N.v47777.
  unfold R.v16484, N.v16484.
  rewrite ?node_47776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47778 (s : N.State) (i : N.Inputs) :
  R.v47778 (state s) (inputs i) = Zmod.unsigned (N.v47778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47778 s i)) at 1.
  unfold R.v47778, N.v47778.
  rewrite ?node_47771.
  rewrite ?node_47772.
  rewrite ?node_47773.
  rewrite ?node_47777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47779 (s : N.State) (i : N.Inputs) :
  R.v47779 (state s) (inputs i) = Zmod.unsigned (N.v47779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47779 s i)) at 1.
  unfold R.v47779, N.v47779.
  unfold R.v6, N.v6.
  rewrite ?node_47778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47780 (s : N.State) (i : N.Inputs) :
  R.v47780 (state s) (inputs i) = Zmod.unsigned (N.v47780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47780 s i)) at 1.
  unfold R.v47780, N.v47780.
  rewrite ?node_15307.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47781 (s : N.State) (i : N.Inputs) :
  R.v47781 (state s) (inputs i) = Zmod.unsigned (N.v47781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47781 s i)) at 1.
  unfold R.v47781, N.v47781.
  unfold R.v6, N.v6.
  rewrite ?node_15372.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47782 (s : N.State) (i : N.Inputs) :
  R.v47782 (state s) (inputs i) = Zmod.unsigned (N.v47782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47782 s i)) at 1.
  unfold R.v47782, N.v47782.
  unfold R.v6, N.v6.
  rewrite ?node_15384.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47783 (s : N.State) (i : N.Inputs) :
  R.v47783 (state s) (inputs i) = Zmod.unsigned (N.v47783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47783 s i)) at 1.
  unfold R.v47783, N.v47783.
  rewrite ?node_47780.
  rewrite ?node_47781.
  rewrite ?node_47782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47784 (s : N.State) (i : N.Inputs) :
  R.v47784 (state s) (inputs i) = Zmod.unsigned (N.v47784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47784 s i)) at 1.
  unfold R.v47784, N.v47784.
  rewrite ?node_47779.
  rewrite ?node_47783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47785 (s : N.State) (i : N.Inputs) :
  R.v47785 (state s) (inputs i) = Zmod.unsigned (N.v47785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47785 s i)) at 1.
  unfold R.v47785, N.v47785.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47786 (s : N.State) (i : N.Inputs) :
  R.v47786 (state s) (inputs i) = Zmod.unsigned (N.v47786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47786 s i)) at 1.
  unfold R.v47786, N.v47786.
  rewrite ?node_15300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47787 (s : N.State) (i : N.Inputs) :
  R.v47787 (state s) (inputs i) = Zmod.unsigned (N.v47787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47787 s i)) at 1.
  unfold R.v47787, N.v47787.
  unfold R.v6, N.v6.
  rewrite ?node_15296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47788 (s : N.State) (i : N.Inputs) :
  R.v47788 (state s) (inputs i) = Zmod.unsigned (N.v47788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47788 s i)) at 1.
  unfold R.v47788, N.v47788.
  unfold R.v6, N.v6.
  rewrite ?node_15293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47789 (s : N.State) (i : N.Inputs) :
  R.v47789 (state s) (inputs i) = Zmod.unsigned (N.v47789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47789 s i)) at 1.
  unfold R.v47789, N.v47789.
  rewrite ?node_47787.
  rewrite ?node_47788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47790 (s : N.State) (i : N.Inputs) :
  R.v47790 (state s) (inputs i) = Zmod.unsigned (N.v47790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47790 s i)) at 1.
  unfold R.v47790, N.v47790.
  unfold R.v16484, N.v16484.
  rewrite ?node_47789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47791 (s : N.State) (i : N.Inputs) :
  R.v47791 (state s) (inputs i) = Zmod.unsigned (N.v47791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47791 s i)) at 1.
  unfold R.v47791, N.v47791.
  rewrite ?node_47786.
  rewrite ?node_47790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47792 (s : N.State) (i : N.Inputs) :
  R.v47792 (state s) (inputs i) = Zmod.unsigned (N.v47792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47792 s i)) at 1.
  unfold R.v47792, N.v47792.
  unfold R.v6, N.v6.
  rewrite ?node_47791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47793 (s : N.State) (i : N.Inputs) :
  R.v47793 (state s) (inputs i) = Zmod.unsigned (N.v47793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47793 s i)) at 1.
  unfold R.v47793, N.v47793.
  rewrite ?node_15301.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47794 (s : N.State) (i : N.Inputs) :
  R.v47794 (state s) (inputs i) = Zmod.unsigned (N.v47794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47794 s i)) at 1.
  unfold R.v47794, N.v47794.
  unfold R.v6, N.v6.
  rewrite ?node_15372.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47795 (s : N.State) (i : N.Inputs) :
  R.v47795 (state s) (inputs i) = Zmod.unsigned (N.v47795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47795 s i)) at 1.
  unfold R.v47795, N.v47795.
  rewrite ?node_47793.
  rewrite ?node_47794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47796 (s : N.State) (i : N.Inputs) :
  R.v47796 (state s) (inputs i) = Zmod.unsigned (N.v47796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47796 s i)) at 1.
  unfold R.v47796, N.v47796.
  rewrite ?node_47792.
  rewrite ?node_47795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47797 (s : N.State) (i : N.Inputs) :
  R.v47797 (state s) (inputs i) = Zmod.unsigned (N.v47797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47797 s i)) at 1.
  unfold R.v47797, N.v47797.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47798 (s : N.State) (i : N.Inputs) :
  R.v47798 (state s) (inputs i) = Zmod.unsigned (N.v47798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47798 s i)) at 1.
  unfold R.v47798, N.v47798.
  rewrite ?node_15306.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47799 (s : N.State) (i : N.Inputs) :
  R.v47799 (state s) (inputs i) = Zmod.unsigned (N.v47799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47799 s i)) at 1.
  unfold R.v47799, N.v47799.
  unfold R.v6, N.v6.
  rewrite ?node_15302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47800 (s : N.State) (i : N.Inputs) :
  R.v47800 (state s) (inputs i) = Zmod.unsigned (N.v47800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47800 s i)) at 1.
  unfold R.v47800, N.v47800.
  unfold R.v6, N.v6.
  rewrite ?node_15301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47801 (s : N.State) (i : N.Inputs) :
  R.v47801 (state s) (inputs i) = Zmod.unsigned (N.v47801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47801 s i)) at 1.
  unfold R.v47801, N.v47801.
  rewrite ?node_47799.
  rewrite ?node_47800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47802 (s : N.State) (i : N.Inputs) :
  R.v47802 (state s) (inputs i) = Zmod.unsigned (N.v47802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47802 s i)) at 1.
  unfold R.v47802, N.v47802.
  unfold R.v16484, N.v16484.
  rewrite ?node_47801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47803 (s : N.State) (i : N.Inputs) :
  R.v47803 (state s) (inputs i) = Zmod.unsigned (N.v47803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47803 s i)) at 1.
  unfold R.v47803, N.v47803.
  rewrite ?node_47798.
  rewrite ?node_47802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47804 (s : N.State) (i : N.Inputs) :
  R.v47804 (state s) (inputs i) = Zmod.unsigned (N.v47804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47804 s i)) at 1.
  unfold R.v47804, N.v47804.
  unfold R.v6, N.v6.
  rewrite ?node_47803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47805 (s : N.State) (i : N.Inputs) :
  R.v47805 (state s) (inputs i) = Zmod.unsigned (N.v47805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47805 s i)) at 1.
  unfold R.v47805, N.v47805.
  rewrite ?node_15307.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47806 (s : N.State) (i : N.Inputs) :
  R.v47806 (state s) (inputs i) = Zmod.unsigned (N.v47806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47806 s i)) at 1.
  unfold R.v47806, N.v47806.
  unfold R.v6, N.v6.
  rewrite ?node_15384.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47807 (s : N.State) (i : N.Inputs) :
  R.v47807 (state s) (inputs i) = Zmod.unsigned (N.v47807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47807 s i)) at 1.
  unfold R.v47807, N.v47807.
  rewrite ?node_47805.
  rewrite ?node_47806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47808 (s : N.State) (i : N.Inputs) :
  R.v47808 (state s) (inputs i) = Zmod.unsigned (N.v47808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47808 s i)) at 1.
  unfold R.v47808, N.v47808.
  rewrite ?node_47804.
  rewrite ?node_47807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47809 (s : N.State) (i : N.Inputs) :
  R.v47809 (state s) (inputs i) = Zmod.unsigned (N.v47809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47809 s i)) at 1.
  unfold R.v47809, N.v47809.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47810 (s : N.State) (i : N.Inputs) :
  R.v47810 (state s) (inputs i) = Zmod.unsigned (N.v47810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47810 s i)) at 1.
  unfold R.v47810, N.v47810.
  rewrite ?node_15356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47811 (s : N.State) (i : N.Inputs) :
  R.v47811 (state s) (inputs i) = Zmod.unsigned (N.v47811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47811 s i)) at 1.
  unfold R.v47811, N.v47811.
  unfold R.v16463, N.v16463.
  rewrite !state_r2134_nr_5F2154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2134_nr_5F2154 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47812 (s : N.State) (i : N.Inputs) :
  R.v47812 (state s) (inputs i) = Zmod.unsigned (N.v47812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47812 s i)) at 1.
  unfold R.v47812, N.v47812.
  rewrite ?node_15351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47813 (s : N.State) (i : N.Inputs) :
  R.v47813 (state s) (inputs i) = Zmod.unsigned (N.v47813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47813 s i)) at 1.
  unfold R.v47813, N.v47813.
  unfold R.v6, N.v6.
  rewrite ?node_15343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47814 (s : N.State) (i : N.Inputs) :
  R.v47814 (state s) (inputs i) = Zmod.unsigned (N.v47814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47814 s i)) at 1.
  unfold R.v47814, N.v47814.
  unfold R.v6, N.v6.
  rewrite ?node_15336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47815 (s : N.State) (i : N.Inputs) :
  R.v47815 (state s) (inputs i) = Zmod.unsigned (N.v47815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47815 s i)) at 1.
  unfold R.v47815, N.v47815.
  rewrite ?node_47813.
  rewrite ?node_47814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47816 (s : N.State) (i : N.Inputs) :
  R.v47816 (state s) (inputs i) = Zmod.unsigned (N.v47816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47816 s i)) at 1.
  unfold R.v47816, N.v47816.
  unfold R.v16484, N.v16484.
  rewrite ?node_47815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47817 (s : N.State) (i : N.Inputs) :
  R.v47817 (state s) (inputs i) = Zmod.unsigned (N.v47817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47817 s i)) at 1.
  unfold R.v47817, N.v47817.
  rewrite ?node_47810.
  rewrite ?node_47811.
  rewrite ?node_47812.
  rewrite ?node_47816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47818 (s : N.State) (i : N.Inputs) :
  R.v47818 (state s) (inputs i) = Zmod.unsigned (N.v47818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47818 s i)) at 1.
  unfold R.v47818, N.v47818.
  unfold R.v6, N.v6.
  rewrite ?node_47817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47819 (s : N.State) (i : N.Inputs) :
  R.v47819 (state s) (inputs i) = Zmod.unsigned (N.v47819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47819 s i)) at 1.
  unfold R.v47819, N.v47819.
  rewrite ?node_15357.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47820 (s : N.State) (i : N.Inputs) :
  R.v47820 (state s) (inputs i) = Zmod.unsigned (N.v47820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47820 s i)) at 1.
  unfold R.v47820, N.v47820.
  unfold R.v6, N.v6.
  rewrite ?node_15423.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47821 (s : N.State) (i : N.Inputs) :
  R.v47821 (state s) (inputs i) = Zmod.unsigned (N.v47821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47821 s i)) at 1.
  unfold R.v47821, N.v47821.
  unfold R.v6, N.v6.
  rewrite ?node_15435.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47822 (s : N.State) (i : N.Inputs) :
  R.v47822 (state s) (inputs i) = Zmod.unsigned (N.v47822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47822 s i)) at 1.
  unfold R.v47822, N.v47822.
  rewrite ?node_47819.
  rewrite ?node_47820.
  rewrite ?node_47821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47823 (s : N.State) (i : N.Inputs) :
  R.v47823 (state s) (inputs i) = Zmod.unsigned (N.v47823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47823 s i)) at 1.
  unfold R.v47823, N.v47823.
  rewrite ?node_47818.
  rewrite ?node_47822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47824 (s : N.State) (i : N.Inputs) :
  R.v47824 (state s) (inputs i) = Zmod.unsigned (N.v47824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47824 s i)) at 1.
  unfold R.v47824, N.v47824.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47825 (s : N.State) (i : N.Inputs) :
  R.v47825 (state s) (inputs i) = Zmod.unsigned (N.v47825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47825 s i)) at 1.
  unfold R.v47825, N.v47825.
  rewrite ?node_15351.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47826 (s : N.State) (i : N.Inputs) :
  R.v47826 (state s) (inputs i) = Zmod.unsigned (N.v47826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47826 s i)) at 1.
  unfold R.v47826, N.v47826.
  unfold R.v6, N.v6.
  rewrite ?node_15343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47827 (s : N.State) (i : N.Inputs) :
  R.v47827 (state s) (inputs i) = Zmod.unsigned (N.v47827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47827 s i)) at 1.
  unfold R.v47827, N.v47827.
  unfold R.v6, N.v6.
  rewrite ?node_15336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47828 (s : N.State) (i : N.Inputs) :
  R.v47828 (state s) (inputs i) = Zmod.unsigned (N.v47828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47828 s i)) at 1.
  unfold R.v47828, N.v47828.
  rewrite ?node_47826.
  rewrite ?node_47827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47829 (s : N.State) (i : N.Inputs) :
  R.v47829 (state s) (inputs i) = Zmod.unsigned (N.v47829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47829 s i)) at 1.
  unfold R.v47829, N.v47829.
  unfold R.v16484, N.v16484.
  rewrite ?node_47828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47830 (s : N.State) (i : N.Inputs) :
  R.v47830 (state s) (inputs i) = Zmod.unsigned (N.v47830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47830 s i)) at 1.
  unfold R.v47830, N.v47830.
  rewrite ?node_47825.
  rewrite ?node_47829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47831 (s : N.State) (i : N.Inputs) :
  R.v47831 (state s) (inputs i) = Zmod.unsigned (N.v47831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47831 s i)) at 1.
  unfold R.v47831, N.v47831.
  unfold R.v6, N.v6.
  rewrite ?node_47830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47832 (s : N.State) (i : N.Inputs) :
  R.v47832 (state s) (inputs i) = Zmod.unsigned (N.v47832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47832 s i)) at 1.
  unfold R.v47832, N.v47832.
  rewrite ?node_15352.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47833 (s : N.State) (i : N.Inputs) :
  R.v47833 (state s) (inputs i) = Zmod.unsigned (N.v47833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47833 s i)) at 1.
  unfold R.v47833, N.v47833.
  unfold R.v6, N.v6.
  rewrite ?node_15423.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47834 (s : N.State) (i : N.Inputs) :
  R.v47834 (state s) (inputs i) = Zmod.unsigned (N.v47834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47834 s i)) at 1.
  unfold R.v47834, N.v47834.
  rewrite ?node_47832.
  rewrite ?node_47833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47835 (s : N.State) (i : N.Inputs) :
  R.v47835 (state s) (inputs i) = Zmod.unsigned (N.v47835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47835 s i)) at 1.
  unfold R.v47835, N.v47835.
  rewrite ?node_47831.
  rewrite ?node_47834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47836 (s : N.State) (i : N.Inputs) :
  R.v47836 (state s) (inputs i) = Zmod.unsigned (N.v47836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47836 s i)) at 1.
  unfold R.v47836, N.v47836.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47837 (s : N.State) (i : N.Inputs) :
  R.v47837 (state s) (inputs i) = Zmod.unsigned (N.v47837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47837 s i)) at 1.
  unfold R.v47837, N.v47837.
  rewrite ?node_15356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47838 (s : N.State) (i : N.Inputs) :
  R.v47838 (state s) (inputs i) = Zmod.unsigned (N.v47838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47838 s i)) at 1.
  unfold R.v47838, N.v47838.
  unfold R.v6, N.v6.
  rewrite !state_r2134_nr_5F2154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2134_nr_5F2154 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47839 (s : N.State) (i : N.Inputs) :
  R.v47839 (state s) (inputs i) = Zmod.unsigned (N.v47839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47839 s i)) at 1.
  unfold R.v47839, N.v47839.
  unfold R.v6, N.v6.
  rewrite ?node_15352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47840 (s : N.State) (i : N.Inputs) :
  R.v47840 (state s) (inputs i) = Zmod.unsigned (N.v47840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47840 s i)) at 1.
  unfold R.v47840, N.v47840.
  rewrite ?node_47838.
  rewrite ?node_47839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47841 (s : N.State) (i : N.Inputs) :
  R.v47841 (state s) (inputs i) = Zmod.unsigned (N.v47841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47841 s i)) at 1.
  unfold R.v47841, N.v47841.
  unfold R.v16484, N.v16484.
  rewrite ?node_47840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47842 (s : N.State) (i : N.Inputs) :
  R.v47842 (state s) (inputs i) = Zmod.unsigned (N.v47842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47842 s i)) at 1.
  unfold R.v47842, N.v47842.
  rewrite ?node_47837.
  rewrite ?node_47841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47843 (s : N.State) (i : N.Inputs) :
  R.v47843 (state s) (inputs i) = Zmod.unsigned (N.v47843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47843 s i)) at 1.
  unfold R.v47843, N.v47843.
  unfold R.v6, N.v6.
  rewrite ?node_47842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47844 (s : N.State) (i : N.Inputs) :
  R.v47844 (state s) (inputs i) = Zmod.unsigned (N.v47844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47844 s i)) at 1.
  unfold R.v47844, N.v47844.
  rewrite ?node_15357.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47845 (s : N.State) (i : N.Inputs) :
  R.v47845 (state s) (inputs i) = Zmod.unsigned (N.v47845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47845 s i)) at 1.
  unfold R.v47845, N.v47845.
  unfold R.v6, N.v6.
  rewrite ?node_15435.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47846 (s : N.State) (i : N.Inputs) :
  R.v47846 (state s) (inputs i) = Zmod.unsigned (N.v47846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47846 s i)) at 1.
  unfold R.v47846, N.v47846.
  rewrite ?node_47844.
  rewrite ?node_47845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47847 (s : N.State) (i : N.Inputs) :
  R.v47847 (state s) (inputs i) = Zmod.unsigned (N.v47847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47847 s i)) at 1.
  unfold R.v47847, N.v47847.
  rewrite ?node_47843.
  rewrite ?node_47846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47848 (s : N.State) (i : N.Inputs) :
  R.v47848 (state s) (inputs i) = Zmod.unsigned (N.v47848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47848 s i)) at 1.
  unfold R.v47848, N.v47848.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47849 (s : N.State) (i : N.Inputs) :
  R.v47849 (state s) (inputs i) = Zmod.unsigned (N.v47849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47849 s i)) at 1.
  unfold R.v47849, N.v47849.
  rewrite ?node_15367.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47850 (s : N.State) (i : N.Inputs) :
  R.v47850 (state s) (inputs i) = Zmod.unsigned (N.v47850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47850 s i)) at 1.
  unfold R.v47850, N.v47850.
  unfold R.v6, N.v6.
  rewrite ?node_15363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47851 (s : N.State) (i : N.Inputs) :
  R.v47851 (state s) (inputs i) = Zmod.unsigned (N.v47851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47851 s i)) at 1.
  unfold R.v47851, N.v47851.
  unfold R.v6, N.v6.
  rewrite ?node_15360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47852 (s : N.State) (i : N.Inputs) :
  R.v47852 (state s) (inputs i) = Zmod.unsigned (N.v47852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47852 s i)) at 1.
  unfold R.v47852, N.v47852.
  rewrite ?node_47850.
  rewrite ?node_47851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47853 (s : N.State) (i : N.Inputs) :
  R.v47853 (state s) (inputs i) = Zmod.unsigned (N.v47853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47853 s i)) at 1.
  unfold R.v47853, N.v47853.
  unfold R.v16484, N.v16484.
  rewrite ?node_47852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47854 (s : N.State) (i : N.Inputs) :
  R.v47854 (state s) (inputs i) = Zmod.unsigned (N.v47854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47854 s i)) at 1.
  unfold R.v47854, N.v47854.
  rewrite ?node_47849.
  rewrite ?node_47853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47855 (s : N.State) (i : N.Inputs) :
  R.v47855 (state s) (inputs i) = Zmod.unsigned (N.v47855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47855 s i)) at 1.
  unfold R.v47855, N.v47855.
  unfold R.v6, N.v6.
  rewrite ?node_47854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47856 (s : N.State) (i : N.Inputs) :
  R.v47856 (state s) (inputs i) = Zmod.unsigned (N.v47856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47856 s i)) at 1.
  unfold R.v47856, N.v47856.
  rewrite ?node_15368.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47857 (s : N.State) (i : N.Inputs) :
  R.v47857 (state s) (inputs i) = Zmod.unsigned (N.v47857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47857 s i)) at 1.
  unfold R.v47857, N.v47857.
  unfold R.v6, N.v6.
  rewrite ?node_15439.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47858 (s : N.State) (i : N.Inputs) :
  R.v47858 (state s) (inputs i) = Zmod.unsigned (N.v47858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47858 s i)) at 1.
  unfold R.v47858, N.v47858.
  rewrite ?node_47856.
  rewrite ?node_47857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47859 (s : N.State) (i : N.Inputs) :
  R.v47859 (state s) (inputs i) = Zmod.unsigned (N.v47859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47859 s i)) at 1.
  unfold R.v47859, N.v47859.
  rewrite ?node_47855.
  rewrite ?node_47858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47860 (s : N.State) (i : N.Inputs) :
  R.v47860 (state s) (inputs i) = Zmod.unsigned (N.v47860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47860 s i)) at 1.
  unfold R.v47860, N.v47860.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47861 (s : N.State) (i : N.Inputs) :
  R.v47861 (state s) (inputs i) = Zmod.unsigned (N.v47861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47861 s i)) at 1.
  unfold R.v47861, N.v47861.
  rewrite ?node_15423.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47862 (s : N.State) (i : N.Inputs) :
  R.v47862 (state s) (inputs i) = Zmod.unsigned (N.v47862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47862 s i)) at 1.
  unfold R.v47862, N.v47862.
  rewrite ?node_15419.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47863 (s : N.State) (i : N.Inputs) :
  R.v47863 (state s) (inputs i) = Zmod.unsigned (N.v47863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47863 s i)) at 1.
  unfold R.v47863, N.v47863.
  rewrite ?node_15415.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47864 (s : N.State) (i : N.Inputs) :
  R.v47864 (state s) (inputs i) = Zmod.unsigned (N.v47864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47864 s i)) at 1.
  unfold R.v47864, N.v47864.
  unfold R.v6, N.v6.
  rewrite ?node_15407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47865 (s : N.State) (i : N.Inputs) :
  R.v47865 (state s) (inputs i) = Zmod.unsigned (N.v47865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47865 s i)) at 1.
  unfold R.v47865, N.v47865.
  unfold R.v6, N.v6.
  rewrite ?node_15400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47866 (s : N.State) (i : N.Inputs) :
  R.v47866 (state s) (inputs i) = Zmod.unsigned (N.v47866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47866 s i)) at 1.
  unfold R.v47866, N.v47866.
  rewrite ?node_47864.
  rewrite ?node_47865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47867 (s : N.State) (i : N.Inputs) :
  R.v47867 (state s) (inputs i) = Zmod.unsigned (N.v47867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47867 s i)) at 1.
  unfold R.v47867, N.v47867.
  unfold R.v16484, N.v16484.
  rewrite ?node_47866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47868 (s : N.State) (i : N.Inputs) :
  R.v47868 (state s) (inputs i) = Zmod.unsigned (N.v47868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47868 s i)) at 1.
  unfold R.v47868, N.v47868.
  rewrite ?node_47861.
  rewrite ?node_47862.
  rewrite ?node_47863.
  rewrite ?node_47867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47869 (s : N.State) (i : N.Inputs) :
  R.v47869 (state s) (inputs i) = Zmod.unsigned (N.v47869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47869 s i)) at 1.
  unfold R.v47869, N.v47869.
  unfold R.v6, N.v6.
  rewrite ?node_47868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47870 (s : N.State) (i : N.Inputs) :
  R.v47870 (state s) (inputs i) = Zmod.unsigned (N.v47870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47870 s i)) at 1.
  unfold R.v47870, N.v47870.
  rewrite ?node_15424.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47871 (s : N.State) (i : N.Inputs) :
  R.v47871 (state s) (inputs i) = Zmod.unsigned (N.v47871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47871 s i)) at 1.
  unfold R.v47871, N.v47871.
  unfold R.v6, N.v6.
  rewrite ?node_15485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47872 (s : N.State) (i : N.Inputs) :
  R.v47872 (state s) (inputs i) = Zmod.unsigned (N.v47872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47872 s i)) at 1.
  unfold R.v47872, N.v47872.
  unfold R.v6, N.v6.
  rewrite ?node_15497.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47873 (s : N.State) (i : N.Inputs) :
  R.v47873 (state s) (inputs i) = Zmod.unsigned (N.v47873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47873 s i)) at 1.
  unfold R.v47873, N.v47873.
  rewrite ?node_47870.
  rewrite ?node_47871.
  rewrite ?node_47872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47874 (s : N.State) (i : N.Inputs) :
  R.v47874 (state s) (inputs i) = Zmod.unsigned (N.v47874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47874 s i)) at 1.
  unfold R.v47874, N.v47874.
  rewrite ?node_47869.
  rewrite ?node_47873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47875 (s : N.State) (i : N.Inputs) :
  R.v47875 (state s) (inputs i) = Zmod.unsigned (N.v47875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47875 s i)) at 1.
  unfold R.v47875, N.v47875.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47876 (s : N.State) (i : N.Inputs) :
  R.v47876 (state s) (inputs i) = Zmod.unsigned (N.v47876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47876 s i)) at 1.
  unfold R.v47876, N.v47876.
  rewrite ?node_15415.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47877 (s : N.State) (i : N.Inputs) :
  R.v47877 (state s) (inputs i) = Zmod.unsigned (N.v47877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47877 s i)) at 1.
  unfold R.v47877, N.v47877.
  unfold R.v6, N.v6.
  rewrite ?node_15407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47878 (s : N.State) (i : N.Inputs) :
  R.v47878 (state s) (inputs i) = Zmod.unsigned (N.v47878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47878 s i)) at 1.
  unfold R.v47878, N.v47878.
  unfold R.v6, N.v6.
  rewrite ?node_15400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47879 (s : N.State) (i : N.Inputs) :
  R.v47879 (state s) (inputs i) = Zmod.unsigned (N.v47879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47879 s i)) at 1.
  unfold R.v47879, N.v47879.
  rewrite ?node_47877.
  rewrite ?node_47878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47880 (s : N.State) (i : N.Inputs) :
  R.v47880 (state s) (inputs i) = Zmod.unsigned (N.v47880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47880 s i)) at 1.
  unfold R.v47880, N.v47880.
  unfold R.v16484, N.v16484.
  rewrite ?node_47879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47881 (s : N.State) (i : N.Inputs) :
  R.v47881 (state s) (inputs i) = Zmod.unsigned (N.v47881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47881 s i)) at 1.
  unfold R.v47881, N.v47881.
  rewrite ?node_47876.
  rewrite ?node_47880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47882 (s : N.State) (i : N.Inputs) :
  R.v47882 (state s) (inputs i) = Zmod.unsigned (N.v47882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47882 s i)) at 1.
  unfold R.v47882, N.v47882.
  unfold R.v6, N.v6.
  rewrite ?node_47881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47883 (s : N.State) (i : N.Inputs) :
  R.v47883 (state s) (inputs i) = Zmod.unsigned (N.v47883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47883 s i)) at 1.
  unfold R.v47883, N.v47883.
  rewrite ?node_15416.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47884 (s : N.State) (i : N.Inputs) :
  R.v47884 (state s) (inputs i) = Zmod.unsigned (N.v47884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47884 s i)) at 1.
  unfold R.v47884, N.v47884.
  unfold R.v6, N.v6.
  rewrite ?node_15485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47885 (s : N.State) (i : N.Inputs) :
  R.v47885 (state s) (inputs i) = Zmod.unsigned (N.v47885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47885 s i)) at 1.
  unfold R.v47885, N.v47885.
  rewrite ?node_47883.
  rewrite ?node_47884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47886 (s : N.State) (i : N.Inputs) :
  R.v47886 (state s) (inputs i) = Zmod.unsigned (N.v47886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47886 s i)) at 1.
  unfold R.v47886, N.v47886.
  rewrite ?node_47882.
  rewrite ?node_47885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47887 (s : N.State) (i : N.Inputs) :
  R.v47887 (state s) (inputs i) = Zmod.unsigned (N.v47887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47887 s i)) at 1.
  unfold R.v47887, N.v47887.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47888 (s : N.State) (i : N.Inputs) :
  R.v47888 (state s) (inputs i) = Zmod.unsigned (N.v47888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47888 s i)) at 1.
  unfold R.v47888, N.v47888.
  rewrite ?node_15423.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47889 (s : N.State) (i : N.Inputs) :
  R.v47889 (state s) (inputs i) = Zmod.unsigned (N.v47889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47889 s i)) at 1.
  unfold R.v47889, N.v47889.
  unfold R.v6, N.v6.
  rewrite ?node_15419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47890 (s : N.State) (i : N.Inputs) :
  R.v47890 (state s) (inputs i) = Zmod.unsigned (N.v47890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47890 s i)) at 1.
  unfold R.v47890, N.v47890.
  unfold R.v6, N.v6.
  rewrite ?node_15416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47891 (s : N.State) (i : N.Inputs) :
  R.v47891 (state s) (inputs i) = Zmod.unsigned (N.v47891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47891 s i)) at 1.
  unfold R.v47891, N.v47891.
  rewrite ?node_47889.
  rewrite ?node_47890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47892 (s : N.State) (i : N.Inputs) :
  R.v47892 (state s) (inputs i) = Zmod.unsigned (N.v47892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47892 s i)) at 1.
  unfold R.v47892, N.v47892.
  unfold R.v16484, N.v16484.
  rewrite ?node_47891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47893 (s : N.State) (i : N.Inputs) :
  R.v47893 (state s) (inputs i) = Zmod.unsigned (N.v47893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47893 s i)) at 1.
  unfold R.v47893, N.v47893.
  rewrite ?node_47888.
  rewrite ?node_47892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47894 (s : N.State) (i : N.Inputs) :
  R.v47894 (state s) (inputs i) = Zmod.unsigned (N.v47894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47894 s i)) at 1.
  unfold R.v47894, N.v47894.
  unfold R.v6, N.v6.
  rewrite ?node_47893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47895 (s : N.State) (i : N.Inputs) :
  R.v47895 (state s) (inputs i) = Zmod.unsigned (N.v47895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47895 s i)) at 1.
  unfold R.v47895, N.v47895.
  rewrite ?node_15424.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47896 (s : N.State) (i : N.Inputs) :
  R.v47896 (state s) (inputs i) = Zmod.unsigned (N.v47896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47896 s i)) at 1.
  unfold R.v47896, N.v47896.
  unfold R.v6, N.v6.
  rewrite ?node_15497.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47897 (s : N.State) (i : N.Inputs) :
  R.v47897 (state s) (inputs i) = Zmod.unsigned (N.v47897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47897 s i)) at 1.
  unfold R.v47897, N.v47897.
  rewrite ?node_47895.
  rewrite ?node_47896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47898 (s : N.State) (i : N.Inputs) :
  R.v47898 (state s) (inputs i) = Zmod.unsigned (N.v47898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47898 s i)) at 1.
  unfold R.v47898, N.v47898.
  rewrite ?node_47894.
  rewrite ?node_47897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47899 (s : N.State) (i : N.Inputs) :
  R.v47899 (state s) (inputs i) = Zmod.unsigned (N.v47899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47899 s i)) at 1.
  unfold R.v47899, N.v47899.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47900 (s : N.State) (i : N.Inputs) :
  R.v47900 (state s) (inputs i) = Zmod.unsigned (N.v47900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47900 s i)) at 1.
  unfold R.v47900, N.v47900.
  unfold R.v6, N.v6.
  rewrite ?node_15430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47901 (s : N.State) (i : N.Inputs) :
  R.v47901 (state s) (inputs i) = Zmod.unsigned (N.v47901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47901 s i)) at 1.
  unfold R.v47901, N.v47901.
  unfold R.v6, N.v6.
  rewrite ?node_15427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47902 (s : N.State) (i : N.Inputs) :
  R.v47902 (state s) (inputs i) = Zmod.unsigned (N.v47902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47902 s i)) at 1.
  unfold R.v47902, N.v47902.
  rewrite ?node_47900.
  rewrite ?node_47901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47903 (s : N.State) (i : N.Inputs) :
  R.v47903 (state s) (inputs i) = Zmod.unsigned (N.v47903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47903 s i)) at 1.
  unfold R.v47903, N.v47903.
  unfold R.v16463, N.v16463.
  rewrite ?node_47902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47904 (s : N.State) (i : N.Inputs) :
  R.v47904 (state s) (inputs i) = Zmod.unsigned (N.v47904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47904 s i)) at 1.
  unfold R.v47904, N.v47904.
  rewrite ?node_15431.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47905 (s : N.State) (i : N.Inputs) :
  R.v47905 (state s) (inputs i) = Zmod.unsigned (N.v47905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47905 s i)) at 1.
  unfold R.v47905, N.v47905.
  unfold R.v6, N.v6.
  rewrite ?node_15499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47906 (s : N.State) (i : N.Inputs) :
  R.v47906 (state s) (inputs i) = Zmod.unsigned (N.v47906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47906 s i)) at 1.
  unfold R.v47906, N.v47906.
  rewrite ?node_47904.
  rewrite ?node_47905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47907 (s : N.State) (i : N.Inputs) :
  R.v47907 (state s) (inputs i) = Zmod.unsigned (N.v47907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47907 s i)) at 1.
  unfold R.v47907, N.v47907.
  rewrite ?node_47903.
  rewrite ?node_47906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47908 (s : N.State) (i : N.Inputs) :
  R.v47908 (state s) (inputs i) = Zmod.unsigned (N.v47908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47908 s i)) at 1.
  unfold R.v47908, N.v47908.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47909 (s : N.State) (i : N.Inputs) :
  R.v47909 (state s) (inputs i) = Zmod.unsigned (N.v47909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47909 s i)) at 1.
  unfold R.v47909, N.v47909.
  rewrite ?node_15485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47910 (s : N.State) (i : N.Inputs) :
  R.v47910 (state s) (inputs i) = Zmod.unsigned (N.v47910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47910 s i)) at 1.
  unfold R.v47910, N.v47910.
  rewrite ?node_15481.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47911 (s : N.State) (i : N.Inputs) :
  R.v47911 (state s) (inputs i) = Zmod.unsigned (N.v47911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47911 s i)) at 1.
  unfold R.v47911, N.v47911.
  rewrite ?node_15477.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47912 (s : N.State) (i : N.Inputs) :
  R.v47912 (state s) (inputs i) = Zmod.unsigned (N.v47912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47912 s i)) at 1.
  unfold R.v47912, N.v47912.
  unfold R.v6, N.v6.
  rewrite ?node_15469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47913 (s : N.State) (i : N.Inputs) :
  R.v47913 (state s) (inputs i) = Zmod.unsigned (N.v47913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47913 s i)) at 1.
  unfold R.v47913, N.v47913.
  unfold R.v6, N.v6.
  rewrite ?node_15462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47914 (s : N.State) (i : N.Inputs) :
  R.v47914 (state s) (inputs i) = Zmod.unsigned (N.v47914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47914 s i)) at 1.
  unfold R.v47914, N.v47914.
  rewrite ?node_47912.
  rewrite ?node_47913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47915 (s : N.State) (i : N.Inputs) :
  R.v47915 (state s) (inputs i) = Zmod.unsigned (N.v47915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47915 s i)) at 1.
  unfold R.v47915, N.v47915.
  unfold R.v16484, N.v16484.
  rewrite ?node_47914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47916 (s : N.State) (i : N.Inputs) :
  R.v47916 (state s) (inputs i) = Zmod.unsigned (N.v47916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47916 s i)) at 1.
  unfold R.v47916, N.v47916.
  rewrite ?node_47909.
  rewrite ?node_47910.
  rewrite ?node_47911.
  rewrite ?node_47915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47917 (s : N.State) (i : N.Inputs) :
  R.v47917 (state s) (inputs i) = Zmod.unsigned (N.v47917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47917 s i)) at 1.
  unfold R.v47917, N.v47917.
  unfold R.v6, N.v6.
  rewrite ?node_47916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47918 (s : N.State) (i : N.Inputs) :
  R.v47918 (state s) (inputs i) = Zmod.unsigned (N.v47918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47918 s i)) at 1.
  unfold R.v47918, N.v47918.
  rewrite ?node_15486.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47919 (s : N.State) (i : N.Inputs) :
  R.v47919 (state s) (inputs i) = Zmod.unsigned (N.v47919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47919 s i)) at 1.
  unfold R.v47919, N.v47919.
  unfold R.v6, N.v6.
  rewrite ?node_15537.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47920 (s : N.State) (i : N.Inputs) :
  R.v47920 (state s) (inputs i) = Zmod.unsigned (N.v47920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47920 s i)) at 1.
  unfold R.v47920, N.v47920.
  unfold R.v6, N.v6.
  rewrite ?node_15553.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47921 (s : N.State) (i : N.Inputs) :
  R.v47921 (state s) (inputs i) = Zmod.unsigned (N.v47921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47921 s i)) at 1.
  unfold R.v47921, N.v47921.
  rewrite ?node_47918.
  rewrite ?node_47919.
  rewrite ?node_47920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47922 (s : N.State) (i : N.Inputs) :
  R.v47922 (state s) (inputs i) = Zmod.unsigned (N.v47922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47922 s i)) at 1.
  unfold R.v47922, N.v47922.
  rewrite ?node_47917.
  rewrite ?node_47921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47923 (s : N.State) (i : N.Inputs) :
  R.v47923 (state s) (inputs i) = Zmod.unsigned (N.v47923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47923 s i)) at 1.
  unfold R.v47923, N.v47923.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47924 (s : N.State) (i : N.Inputs) :
  R.v47924 (state s) (inputs i) = Zmod.unsigned (N.v47924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47924 s i)) at 1.
  unfold R.v47924, N.v47924.
  rewrite ?node_15477.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47925 (s : N.State) (i : N.Inputs) :
  R.v47925 (state s) (inputs i) = Zmod.unsigned (N.v47925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47925 s i)) at 1.
  unfold R.v47925, N.v47925.
  unfold R.v6, N.v6.
  rewrite ?node_15469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47926 (s : N.State) (i : N.Inputs) :
  R.v47926 (state s) (inputs i) = Zmod.unsigned (N.v47926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47926 s i)) at 1.
  unfold R.v47926, N.v47926.
  unfold R.v6, N.v6.
  rewrite ?node_15462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47927 (s : N.State) (i : N.Inputs) :
  R.v47927 (state s) (inputs i) = Zmod.unsigned (N.v47927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47927 s i)) at 1.
  unfold R.v47927, N.v47927.
  rewrite ?node_47925.
  rewrite ?node_47926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47928 (s : N.State) (i : N.Inputs) :
  R.v47928 (state s) (inputs i) = Zmod.unsigned (N.v47928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47928 s i)) at 1.
  unfold R.v47928, N.v47928.
  unfold R.v16484, N.v16484.
  rewrite ?node_47927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47929 (s : N.State) (i : N.Inputs) :
  R.v47929 (state s) (inputs i) = Zmod.unsigned (N.v47929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47929 s i)) at 1.
  unfold R.v47929, N.v47929.
  rewrite ?node_47924.
  rewrite ?node_47928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47930 (s : N.State) (i : N.Inputs) :
  R.v47930 (state s) (inputs i) = Zmod.unsigned (N.v47930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47930 s i)) at 1.
  unfold R.v47930, N.v47930.
  unfold R.v6, N.v6.
  rewrite ?node_47929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47931 (s : N.State) (i : N.Inputs) :
  R.v47931 (state s) (inputs i) = Zmod.unsigned (N.v47931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47931 s i)) at 1.
  unfold R.v47931, N.v47931.
  rewrite ?node_15478.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47932 (s : N.State) (i : N.Inputs) :
  R.v47932 (state s) (inputs i) = Zmod.unsigned (N.v47932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47932 s i)) at 1.
  unfold R.v47932, N.v47932.
  unfold R.v6, N.v6.
  rewrite ?node_15537.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47933 (s : N.State) (i : N.Inputs) :
  R.v47933 (state s) (inputs i) = Zmod.unsigned (N.v47933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47933 s i)) at 1.
  unfold R.v47933, N.v47933.
  rewrite ?node_47931.
  rewrite ?node_47932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47934 (s : N.State) (i : N.Inputs) :
  R.v47934 (state s) (inputs i) = Zmod.unsigned (N.v47934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47934 s i)) at 1.
  unfold R.v47934, N.v47934.
  rewrite ?node_47930.
  rewrite ?node_47933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47935 (s : N.State) (i : N.Inputs) :
  R.v47935 (state s) (inputs i) = Zmod.unsigned (N.v47935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47935 s i)) at 1.
  unfold R.v47935, N.v47935.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47936 (s : N.State) (i : N.Inputs) :
  R.v47936 (state s) (inputs i) = Zmod.unsigned (N.v47936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47936 s i)) at 1.
  unfold R.v47936, N.v47936.
  rewrite ?node_15485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47937 (s : N.State) (i : N.Inputs) :
  R.v47937 (state s) (inputs i) = Zmod.unsigned (N.v47937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47937 s i)) at 1.
  unfold R.v47937, N.v47937.
  unfold R.v6, N.v6.
  rewrite ?node_15481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47938 (s : N.State) (i : N.Inputs) :
  R.v47938 (state s) (inputs i) = Zmod.unsigned (N.v47938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47938 s i)) at 1.
  unfold R.v47938, N.v47938.
  unfold R.v6, N.v6.
  rewrite ?node_15478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47939 (s : N.State) (i : N.Inputs) :
  R.v47939 (state s) (inputs i) = Zmod.unsigned (N.v47939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47939 s i)) at 1.
  unfold R.v47939, N.v47939.
  rewrite ?node_47937.
  rewrite ?node_47938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47940 (s : N.State) (i : N.Inputs) :
  R.v47940 (state s) (inputs i) = Zmod.unsigned (N.v47940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47940 s i)) at 1.
  unfold R.v47940, N.v47940.
  unfold R.v16484, N.v16484.
  rewrite ?node_47939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47941 (s : N.State) (i : N.Inputs) :
  R.v47941 (state s) (inputs i) = Zmod.unsigned (N.v47941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47941 s i)) at 1.
  unfold R.v47941, N.v47941.
  rewrite ?node_47936.
  rewrite ?node_47940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47942 (s : N.State) (i : N.Inputs) :
  R.v47942 (state s) (inputs i) = Zmod.unsigned (N.v47942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47942 s i)) at 1.
  unfold R.v47942, N.v47942.
  unfold R.v6, N.v6.
  rewrite ?node_47941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47943 (s : N.State) (i : N.Inputs) :
  R.v47943 (state s) (inputs i) = Zmod.unsigned (N.v47943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47943 s i)) at 1.
  unfold R.v47943, N.v47943.
  rewrite ?node_15486.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47944 (s : N.State) (i : N.Inputs) :
  R.v47944 (state s) (inputs i) = Zmod.unsigned (N.v47944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47944 s i)) at 1.
  unfold R.v47944, N.v47944.
  unfold R.v6, N.v6.
  rewrite ?node_15553.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47945 (s : N.State) (i : N.Inputs) :
  R.v47945 (state s) (inputs i) = Zmod.unsigned (N.v47945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47945 s i)) at 1.
  unfold R.v47945, N.v47945.
  rewrite ?node_47943.
  rewrite ?node_47944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47946 (s : N.State) (i : N.Inputs) :
  R.v47946 (state s) (inputs i) = Zmod.unsigned (N.v47946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47946 s i)) at 1.
  unfold R.v47946, N.v47946.
  rewrite ?node_47942.
  rewrite ?node_47945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47947 (s : N.State) (i : N.Inputs) :
  R.v47947 (state s) (inputs i) = Zmod.unsigned (N.v47947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47947 s i)) at 1.
  unfold R.v47947, N.v47947.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47948 (s : N.State) (i : N.Inputs) :
  R.v47948 (state s) (inputs i) = Zmod.unsigned (N.v47948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47948 s i)) at 1.
  unfold R.v47948, N.v47948.
  unfold R.v6, N.v6.
  rewrite ?node_15492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47949 (s : N.State) (i : N.Inputs) :
  R.v47949 (state s) (inputs i) = Zmod.unsigned (N.v47949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47949 s i)) at 1.
  unfold R.v47949, N.v47949.
  unfold R.v6, N.v6.
  rewrite ?node_15489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47950 (s : N.State) (i : N.Inputs) :
  R.v47950 (state s) (inputs i) = Zmod.unsigned (N.v47950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47950 s i)) at 1.
  unfold R.v47950, N.v47950.
  rewrite ?node_47948.
  rewrite ?node_47949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47951 (s : N.State) (i : N.Inputs) :
  R.v47951 (state s) (inputs i) = Zmod.unsigned (N.v47951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47951 s i)) at 1.
  unfold R.v47951, N.v47951.
  unfold R.v16463, N.v16463.
  rewrite ?node_47950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47952 (s : N.State) (i : N.Inputs) :
  R.v47952 (state s) (inputs i) = Zmod.unsigned (N.v47952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47952 s i)) at 1.
  unfold R.v47952, N.v47952.
  rewrite ?node_15493.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47953 (s : N.State) (i : N.Inputs) :
  R.v47953 (state s) (inputs i) = Zmod.unsigned (N.v47953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47953 s i)) at 1.
  unfold R.v47953, N.v47953.
  unfold R.v6, N.v6.
  rewrite ?node_15555.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47954 (s : N.State) (i : N.Inputs) :
  R.v47954 (state s) (inputs i) = Zmod.unsigned (N.v47954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47954 s i)) at 1.
  unfold R.v47954, N.v47954.
  rewrite ?node_47952.
  rewrite ?node_47953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47955 (s : N.State) (i : N.Inputs) :
  R.v47955 (state s) (inputs i) = Zmod.unsigned (N.v47955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47955 s i)) at 1.
  unfold R.v47955, N.v47955.
  rewrite ?node_47951.
  rewrite ?node_47954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47956 (s : N.State) (i : N.Inputs) :
  R.v47956 (state s) (inputs i) = Zmod.unsigned (N.v47956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47956 s i)) at 1.
  unfold R.v47956, N.v47956.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47957 (s : N.State) (i : N.Inputs) :
  R.v47957 (state s) (inputs i) = Zmod.unsigned (N.v47957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47957 s i)) at 1.
  unfold R.v47957, N.v47957.
  rewrite ?node_15537.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47958 (s : N.State) (i : N.Inputs) :
  R.v47958 (state s) (inputs i) = Zmod.unsigned (N.v47958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47958 s i)) at 1.
  unfold R.v47958, N.v47958.
  rewrite ?node_15533.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47959 (s : N.State) (i : N.Inputs) :
  R.v47959 (state s) (inputs i) = Zmod.unsigned (N.v47959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47959 s i)) at 1.
  unfold R.v47959, N.v47959.
  rewrite ?node_15529.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47960 (s : N.State) (i : N.Inputs) :
  R.v47960 (state s) (inputs i) = Zmod.unsigned (N.v47960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47960 s i)) at 1.
  unfold R.v47960, N.v47960.
  unfold R.v6, N.v6.
  rewrite ?node_15526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47961 (s : N.State) (i : N.Inputs) :
  R.v47961 (state s) (inputs i) = Zmod.unsigned (N.v47961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47961 s i)) at 1.
  unfold R.v47961, N.v47961.
  unfold R.v6, N.v6.
  rewrite ?node_15519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47962 (s : N.State) (i : N.Inputs) :
  R.v47962 (state s) (inputs i) = Zmod.unsigned (N.v47962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47962 s i)) at 1.
  unfold R.v47962, N.v47962.
  rewrite ?node_47960.
  rewrite ?node_47961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47963 (s : N.State) (i : N.Inputs) :
  R.v47963 (state s) (inputs i) = Zmod.unsigned (N.v47963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47963 s i)) at 1.
  unfold R.v47963, N.v47963.
  unfold R.v16484, N.v16484.
  rewrite ?node_47962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47964 (s : N.State) (i : N.Inputs) :
  R.v47964 (state s) (inputs i) = Zmod.unsigned (N.v47964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47964 s i)) at 1.
  unfold R.v47964, N.v47964.
  rewrite ?node_47957.
  rewrite ?node_47958.
  rewrite ?node_47959.
  rewrite ?node_47963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47965 (s : N.State) (i : N.Inputs) :
  R.v47965 (state s) (inputs i) = Zmod.unsigned (N.v47965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47965 s i)) at 1.
  unfold R.v47965, N.v47965.
  unfold R.v6, N.v6.
  rewrite ?node_47964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47966 (s : N.State) (i : N.Inputs) :
  R.v47966 (state s) (inputs i) = Zmod.unsigned (N.v47966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47966 s i)) at 1.
  unfold R.v47966, N.v47966.
  rewrite ?node_15538.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47967 (s : N.State) (i : N.Inputs) :
  R.v47967 (state s) (inputs i) = Zmod.unsigned (N.v47967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47967 s i)) at 1.
  unfold R.v47967, N.v47967.
  unfold R.v6, N.v6.
  rewrite ?node_15594.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47968 (s : N.State) (i : N.Inputs) :
  R.v47968 (state s) (inputs i) = Zmod.unsigned (N.v47968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47968 s i)) at 1.
  unfold R.v47968, N.v47968.
  unfold R.v6, N.v6.
  rewrite ?node_15606.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47969 (s : N.State) (i : N.Inputs) :
  R.v47969 (state s) (inputs i) = Zmod.unsigned (N.v47969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47969 s i)) at 1.
  unfold R.v47969, N.v47969.
  rewrite ?node_47966.
  rewrite ?node_47967.
  rewrite ?node_47968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47970 (s : N.State) (i : N.Inputs) :
  R.v47970 (state s) (inputs i) = Zmod.unsigned (N.v47970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47970 s i)) at 1.
  unfold R.v47970, N.v47970.
  rewrite ?node_47965.
  rewrite ?node_47969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47971 (s : N.State) (i : N.Inputs) :
  R.v47971 (state s) (inputs i) = Zmod.unsigned (N.v47971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47971 s i)) at 1.
  unfold R.v47971, N.v47971.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47972 (s : N.State) (i : N.Inputs) :
  R.v47972 (state s) (inputs i) = Zmod.unsigned (N.v47972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47972 s i)) at 1.
  unfold R.v47972, N.v47972.
  rewrite ?node_15529.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47973 (s : N.State) (i : N.Inputs) :
  R.v47973 (state s) (inputs i) = Zmod.unsigned (N.v47973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47973 s i)) at 1.
  unfold R.v47973, N.v47973.
  unfold R.v6, N.v6.
  rewrite ?node_15526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47974 (s : N.State) (i : N.Inputs) :
  R.v47974 (state s) (inputs i) = Zmod.unsigned (N.v47974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47974 s i)) at 1.
  unfold R.v47974, N.v47974.
  unfold R.v6, N.v6.
  rewrite ?node_15519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47975 (s : N.State) (i : N.Inputs) :
  R.v47975 (state s) (inputs i) = Zmod.unsigned (N.v47975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47975 s i)) at 1.
  unfold R.v47975, N.v47975.
  rewrite ?node_47973.
  rewrite ?node_47974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47976 (s : N.State) (i : N.Inputs) :
  R.v47976 (state s) (inputs i) = Zmod.unsigned (N.v47976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47976 s i)) at 1.
  unfold R.v47976, N.v47976.
  unfold R.v16484, N.v16484.
  rewrite ?node_47975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47977 (s : N.State) (i : N.Inputs) :
  R.v47977 (state s) (inputs i) = Zmod.unsigned (N.v47977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47977 s i)) at 1.
  unfold R.v47977, N.v47977.
  rewrite ?node_47972.
  rewrite ?node_47976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47978 (s : N.State) (i : N.Inputs) :
  R.v47978 (state s) (inputs i) = Zmod.unsigned (N.v47978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47978 s i)) at 1.
  unfold R.v47978, N.v47978.
  unfold R.v6, N.v6.
  rewrite ?node_47977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47979 (s : N.State) (i : N.Inputs) :
  R.v47979 (state s) (inputs i) = Zmod.unsigned (N.v47979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47979 s i)) at 1.
  unfold R.v47979, N.v47979.
  rewrite ?node_15530.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47980 (s : N.State) (i : N.Inputs) :
  R.v47980 (state s) (inputs i) = Zmod.unsigned (N.v47980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47980 s i)) at 1.
  unfold R.v47980, N.v47980.
  unfold R.v6, N.v6.
  rewrite ?node_15594.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47981 (s : N.State) (i : N.Inputs) :
  R.v47981 (state s) (inputs i) = Zmod.unsigned (N.v47981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47981 s i)) at 1.
  unfold R.v47981, N.v47981.
  rewrite ?node_47979.
  rewrite ?node_47980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47982 (s : N.State) (i : N.Inputs) :
  R.v47982 (state s) (inputs i) = Zmod.unsigned (N.v47982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47982 s i)) at 1.
  unfold R.v47982, N.v47982.
  rewrite ?node_47978.
  rewrite ?node_47981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47983 (s : N.State) (i : N.Inputs) :
  R.v47983 (state s) (inputs i) = Zmod.unsigned (N.v47983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47983 s i)) at 1.
  unfold R.v47983, N.v47983.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47984 (s : N.State) (i : N.Inputs) :
  R.v47984 (state s) (inputs i) = Zmod.unsigned (N.v47984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47984 s i)) at 1.
  unfold R.v47984, N.v47984.
  rewrite ?node_15537.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47985 (s : N.State) (i : N.Inputs) :
  R.v47985 (state s) (inputs i) = Zmod.unsigned (N.v47985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47985 s i)) at 1.
  unfold R.v47985, N.v47985.
  unfold R.v6, N.v6.
  rewrite ?node_15533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47986 (s : N.State) (i : N.Inputs) :
  R.v47986 (state s) (inputs i) = Zmod.unsigned (N.v47986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47986 s i)) at 1.
  unfold R.v47986, N.v47986.
  unfold R.v6, N.v6.
  rewrite ?node_15530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47987 (s : N.State) (i : N.Inputs) :
  R.v47987 (state s) (inputs i) = Zmod.unsigned (N.v47987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47987 s i)) at 1.
  unfold R.v47987, N.v47987.
  rewrite ?node_47985.
  rewrite ?node_47986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47988 (s : N.State) (i : N.Inputs) :
  R.v47988 (state s) (inputs i) = Zmod.unsigned (N.v47988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47988 s i)) at 1.
  unfold R.v47988, N.v47988.
  unfold R.v16484, N.v16484.
  rewrite ?node_47987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47989 (s : N.State) (i : N.Inputs) :
  R.v47989 (state s) (inputs i) = Zmod.unsigned (N.v47989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47989 s i)) at 1.
  unfold R.v47989, N.v47989.
  rewrite ?node_47984.
  rewrite ?node_47988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47990 (s : N.State) (i : N.Inputs) :
  R.v47990 (state s) (inputs i) = Zmod.unsigned (N.v47990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47990 s i)) at 1.
  unfold R.v47990, N.v47990.
  unfold R.v6, N.v6.
  rewrite ?node_47989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47991 (s : N.State) (i : N.Inputs) :
  R.v47991 (state s) (inputs i) = Zmod.unsigned (N.v47991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47991 s i)) at 1.
  unfold R.v47991, N.v47991.
  rewrite ?node_15538.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47992 (s : N.State) (i : N.Inputs) :
  R.v47992 (state s) (inputs i) = Zmod.unsigned (N.v47992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47992 s i)) at 1.
  unfold R.v47992, N.v47992.
  unfold R.v6, N.v6.
  rewrite ?node_15606.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47993 (s : N.State) (i : N.Inputs) :
  R.v47993 (state s) (inputs i) = Zmod.unsigned (N.v47993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47993 s i)) at 1.
  unfold R.v47993, N.v47993.
  rewrite ?node_47991.
  rewrite ?node_47992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47994 (s : N.State) (i : N.Inputs) :
  R.v47994 (state s) (inputs i) = Zmod.unsigned (N.v47994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47994 s i)) at 1.
  unfold R.v47994, N.v47994.
  rewrite ?node_47990.
  rewrite ?node_47993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47995 (s : N.State) (i : N.Inputs) :
  R.v47995 (state s) (inputs i) = Zmod.unsigned (N.v47995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47995 s i)) at 1.
  unfold R.v47995, N.v47995.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47996 (s : N.State) (i : N.Inputs) :
  R.v47996 (state s) (inputs i) = Zmod.unsigned (N.v47996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47996 s i)) at 1.
  unfold R.v47996, N.v47996.
  rewrite ?node_15548.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47997 (s : N.State) (i : N.Inputs) :
  R.v47997 (state s) (inputs i) = Zmod.unsigned (N.v47997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47997 s i)) at 1.
  unfold R.v47997, N.v47997.
  unfold R.v6, N.v6.
  rewrite ?node_15544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47998 (s : N.State) (i : N.Inputs) :
  R.v47998 (state s) (inputs i) = Zmod.unsigned (N.v47998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47998 s i)) at 1.
  unfold R.v47998, N.v47998.
  unfold R.v6, N.v6.
  rewrite ?node_15541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47999 (s : N.State) (i : N.Inputs) :
  R.v47999 (state s) (inputs i) = Zmod.unsigned (N.v47999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47999 s i)) at 1.
  unfold R.v47999, N.v47999.
  rewrite ?node_47997.
  rewrite ?node_47998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
