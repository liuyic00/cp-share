(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes036.
Lemma node_37000 (s : N.State) (i : N.Inputs) :
  R.v37000 (state s) (inputs i) = Zmod.unsigned (N.v37000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37000 s i)) at 1.
  unfold R.v37000, N.v37000.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37001 (s : N.State) (i : N.Inputs) :
  R.v37001 (state s) (inputs i) = Zmod.unsigned (N.v37001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37001 s i)) at 1.
  unfold R.v37001, N.v37001.
  rewrite ?node_15737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37002 (s : N.State) (i : N.Inputs) :
  R.v37002 (state s) (inputs i) = Zmod.unsigned (N.v37002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37002 s i)) at 1.
  unfold R.v37002, N.v37002.
  unfold R.v16463, N.v16463.
  rewrite !state_r2205_nr_5F2228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2205_nr_5F2228 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37003 (s : N.State) (i : N.Inputs) :
  R.v37003 (state s) (inputs i) = Zmod.unsigned (N.v37003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37003 s i)) at 1.
  unfold R.v37003, N.v37003.
  unfold R.v16463, N.v16463.
  rewrite !state_r2204_nr_5F2227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2204_nr_5F2227 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37004 (s : N.State) (i : N.Inputs) :
  R.v37004 (state s) (inputs i) = Zmod.unsigned (N.v37004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37004 s i)) at 1.
  unfold R.v37004, N.v37004.
  unfold R.v6, N.v6.
  rewrite !state_r2203_nr_5F2226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2203_nr_5F2226 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37005 (s : N.State) (i : N.Inputs) :
  R.v37005 (state s) (inputs i) = Zmod.unsigned (N.v37005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37005 s i)) at 1.
  unfold R.v37005, N.v37005.
  unfold R.v6, N.v6.
  rewrite !state_r2202_nr_5F2225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2202_nr_5F2225 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37006 (s : N.State) (i : N.Inputs) :
  R.v37006 (state s) (inputs i) = Zmod.unsigned (N.v37006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37006 s i)) at 1.
  unfold R.v37006, N.v37006.
  rewrite ?node_37004.
  rewrite ?node_37005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37007 (s : N.State) (i : N.Inputs) :
  R.v37007 (state s) (inputs i) = Zmod.unsigned (N.v37007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37007 s i)) at 1.
  unfold R.v37007, N.v37007.
  unfold R.v16484, N.v16484.
  rewrite ?node_37006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37008 (s : N.State) (i : N.Inputs) :
  R.v37008 (state s) (inputs i) = Zmod.unsigned (N.v37008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37008 s i)) at 1.
  unfold R.v37008, N.v37008.
  rewrite ?node_37001.
  rewrite ?node_37002.
  rewrite ?node_37003.
  rewrite ?node_37007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37009 (s : N.State) (i : N.Inputs) :
  R.v37009 (state s) (inputs i) = Zmod.unsigned (N.v37009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37009 s i)) at 1.
  unfold R.v37009, N.v37009.
  unfold R.v6, N.v6.
  rewrite ?node_37008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37010 (s : N.State) (i : N.Inputs) :
  R.v37010 (state s) (inputs i) = Zmod.unsigned (N.v37010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37010 s i)) at 1.
  unfold R.v37010, N.v37010.
  rewrite ?node_15738.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37011 (s : N.State) (i : N.Inputs) :
  R.v37011 (state s) (inputs i) = Zmod.unsigned (N.v37011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37011 s i)) at 1.
  unfold R.v37011, N.v37011.
  unfold R.v6, N.v6.
  rewrite ?node_15786.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37012 (s : N.State) (i : N.Inputs) :
  R.v37012 (state s) (inputs i) = Zmod.unsigned (N.v37012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37012 s i)) at 1.
  unfold R.v37012, N.v37012.
  unfold R.v6, N.v6.
  rewrite ?node_15800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37013 (s : N.State) (i : N.Inputs) :
  R.v37013 (state s) (inputs i) = Zmod.unsigned (N.v37013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37013 s i)) at 1.
  unfold R.v37013, N.v37013.
  rewrite ?node_37010.
  rewrite ?node_37011.
  rewrite ?node_37012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37014 (s : N.State) (i : N.Inputs) :
  R.v37014 (state s) (inputs i) = Zmod.unsigned (N.v37014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37014 s i)) at 1.
  unfold R.v37014, N.v37014.
  rewrite ?node_37009.
  rewrite ?node_37013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37015 (s : N.State) (i : N.Inputs) :
  R.v37015 (state s) (inputs i) = Zmod.unsigned (N.v37015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37015 s i)) at 1.
  unfold R.v37015, N.v37015.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37016 (s : N.State) (i : N.Inputs) :
  R.v37016 (state s) (inputs i) = Zmod.unsigned (N.v37016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37016 s i)) at 1.
  unfold R.v37016, N.v37016.
  unfold R.v16463, N.v16463.
  rewrite !state_r2204_nr_5F2227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2204_nr_5F2227 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37017 (s : N.State) (i : N.Inputs) :
  R.v37017 (state s) (inputs i) = Zmod.unsigned (N.v37017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37017 s i)) at 1.
  unfold R.v37017, N.v37017.
  unfold R.v6, N.v6.
  rewrite !state_r2203_nr_5F2226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2203_nr_5F2226 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37018 (s : N.State) (i : N.Inputs) :
  R.v37018 (state s) (inputs i) = Zmod.unsigned (N.v37018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37018 s i)) at 1.
  unfold R.v37018, N.v37018.
  unfold R.v6, N.v6.
  rewrite !state_r2202_nr_5F2225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2202_nr_5F2225 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37019 (s : N.State) (i : N.Inputs) :
  R.v37019 (state s) (inputs i) = Zmod.unsigned (N.v37019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37019 s i)) at 1.
  unfold R.v37019, N.v37019.
  rewrite ?node_37017.
  rewrite ?node_37018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37020 (s : N.State) (i : N.Inputs) :
  R.v37020 (state s) (inputs i) = Zmod.unsigned (N.v37020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37020 s i)) at 1.
  unfold R.v37020, N.v37020.
  unfold R.v16484, N.v16484.
  rewrite ?node_37019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37021 (s : N.State) (i : N.Inputs) :
  R.v37021 (state s) (inputs i) = Zmod.unsigned (N.v37021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37021 s i)) at 1.
  unfold R.v37021, N.v37021.
  rewrite ?node_37016.
  rewrite ?node_37020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37022 (s : N.State) (i : N.Inputs) :
  R.v37022 (state s) (inputs i) = Zmod.unsigned (N.v37022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37022 s i)) at 1.
  unfold R.v37022, N.v37022.
  unfold R.v6, N.v6.
  rewrite ?node_37021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37023 (s : N.State) (i : N.Inputs) :
  R.v37023 (state s) (inputs i) = Zmod.unsigned (N.v37023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37023 s i)) at 1.
  unfold R.v37023, N.v37023.
  rewrite ?node_15733.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37024 (s : N.State) (i : N.Inputs) :
  R.v37024 (state s) (inputs i) = Zmod.unsigned (N.v37024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37024 s i)) at 1.
  unfold R.v37024, N.v37024.
  unfold R.v6, N.v6.
  rewrite ?node_15786.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37025 (s : N.State) (i : N.Inputs) :
  R.v37025 (state s) (inputs i) = Zmod.unsigned (N.v37025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37025 s i)) at 1.
  unfold R.v37025, N.v37025.
  rewrite ?node_37023.
  rewrite ?node_37024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37026 (s : N.State) (i : N.Inputs) :
  R.v37026 (state s) (inputs i) = Zmod.unsigned (N.v37026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37026 s i)) at 1.
  unfold R.v37026, N.v37026.
  rewrite ?node_37022.
  rewrite ?node_37025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37027 (s : N.State) (i : N.Inputs) :
  R.v37027 (state s) (inputs i) = Zmod.unsigned (N.v37027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37027 s i)) at 1.
  unfold R.v37027, N.v37027.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37028 (s : N.State) (i : N.Inputs) :
  R.v37028 (state s) (inputs i) = Zmod.unsigned (N.v37028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37028 s i)) at 1.
  unfold R.v37028, N.v37028.
  rewrite ?node_15737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37029 (s : N.State) (i : N.Inputs) :
  R.v37029 (state s) (inputs i) = Zmod.unsigned (N.v37029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37029 s i)) at 1.
  unfold R.v37029, N.v37029.
  unfold R.v6, N.v6.
  rewrite !state_r2205_nr_5F2228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2205_nr_5F2228 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37030 (s : N.State) (i : N.Inputs) :
  R.v37030 (state s) (inputs i) = Zmod.unsigned (N.v37030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37030 s i)) at 1.
  unfold R.v37030, N.v37030.
  unfold R.v6, N.v6.
  rewrite ?node_15733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37031 (s : N.State) (i : N.Inputs) :
  R.v37031 (state s) (inputs i) = Zmod.unsigned (N.v37031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37031 s i)) at 1.
  unfold R.v37031, N.v37031.
  rewrite ?node_37029.
  rewrite ?node_37030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37032 (s : N.State) (i : N.Inputs) :
  R.v37032 (state s) (inputs i) = Zmod.unsigned (N.v37032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37032 s i)) at 1.
  unfold R.v37032, N.v37032.
  unfold R.v16484, N.v16484.
  rewrite ?node_37031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37033 (s : N.State) (i : N.Inputs) :
  R.v37033 (state s) (inputs i) = Zmod.unsigned (N.v37033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37033 s i)) at 1.
  unfold R.v37033, N.v37033.
  rewrite ?node_37028.
  rewrite ?node_37032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37034 (s : N.State) (i : N.Inputs) :
  R.v37034 (state s) (inputs i) = Zmod.unsigned (N.v37034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37034 s i)) at 1.
  unfold R.v37034, N.v37034.
  unfold R.v6, N.v6.
  rewrite ?node_37033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37035 (s : N.State) (i : N.Inputs) :
  R.v37035 (state s) (inputs i) = Zmod.unsigned (N.v37035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37035 s i)) at 1.
  unfold R.v37035, N.v37035.
  rewrite ?node_15738.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37036 (s : N.State) (i : N.Inputs) :
  R.v37036 (state s) (inputs i) = Zmod.unsigned (N.v37036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37036 s i)) at 1.
  unfold R.v37036, N.v37036.
  unfold R.v6, N.v6.
  rewrite ?node_15800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37037 (s : N.State) (i : N.Inputs) :
  R.v37037 (state s) (inputs i) = Zmod.unsigned (N.v37037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37037 s i)) at 1.
  unfold R.v37037, N.v37037.
  rewrite ?node_37035.
  rewrite ?node_37036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37038 (s : N.State) (i : N.Inputs) :
  R.v37038 (state s) (inputs i) = Zmod.unsigned (N.v37038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37038 s i)) at 1.
  unfold R.v37038, N.v37038.
  rewrite ?node_37034.
  rewrite ?node_37037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37039 (s : N.State) (i : N.Inputs) :
  R.v37039 (state s) (inputs i) = Zmod.unsigned (N.v37039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37039 s i)) at 1.
  unfold R.v37039, N.v37039.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37040 (s : N.State) (i : N.Inputs) :
  R.v37040 (state s) (inputs i) = Zmod.unsigned (N.v37040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37040 s i)) at 1.
  unfold R.v37040, N.v37040.
  rewrite ?node_15779.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37041 (s : N.State) (i : N.Inputs) :
  R.v37041 (state s) (inputs i) = Zmod.unsigned (N.v37041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37041 s i)) at 1.
  unfold R.v37041, N.v37041.
  unfold R.v16463, N.v16463.
  rewrite !state_r2209_nr_5F2233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2209_nr_5F2233 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37042 (s : N.State) (i : N.Inputs) :
  R.v37042 (state s) (inputs i) = Zmod.unsigned (N.v37042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37042 s i)) at 1.
  unfold R.v37042, N.v37042.
  unfold R.v16463, N.v16463.
  rewrite !state_r2208_nr_5F2232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2208_nr_5F2232 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37043 (s : N.State) (i : N.Inputs) :
  R.v37043 (state s) (inputs i) = Zmod.unsigned (N.v37043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37043 s i)) at 1.
  unfold R.v37043, N.v37043.
  unfold R.v6, N.v6.
  rewrite !state_r2207_nr_5F2231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2207_nr_5F2231 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37044 (s : N.State) (i : N.Inputs) :
  R.v37044 (state s) (inputs i) = Zmod.unsigned (N.v37044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37044 s i)) at 1.
  unfold R.v37044, N.v37044.
  unfold R.v19, N.v19.
  rewrite ?node_37043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37045 (s : N.State) (i : N.Inputs) :
  R.v37045 (state s) (inputs i) = Zmod.unsigned (N.v37045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37045 s i)) at 1.
  unfold R.v37045, N.v37045.
  unfold R.v16484, N.v16484.
  rewrite ?node_37044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37046 (s : N.State) (i : N.Inputs) :
  R.v37046 (state s) (inputs i) = Zmod.unsigned (N.v37046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37046 s i)) at 1.
  unfold R.v37046, N.v37046.
  rewrite ?node_37040.
  rewrite ?node_37041.
  rewrite ?node_37042.
  rewrite ?node_37045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37047 (s : N.State) (i : N.Inputs) :
  R.v37047 (state s) (inputs i) = Zmod.unsigned (N.v37047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37047 s i)) at 1.
  unfold R.v37047, N.v37047.
  unfold R.v6, N.v6.
  rewrite ?node_37046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37048 (s : N.State) (i : N.Inputs) :
  R.v37048 (state s) (inputs i) = Zmod.unsigned (N.v37048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37048 s i)) at 1.
  unfold R.v37048, N.v37048.
  rewrite ?node_15780.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37049 (s : N.State) (i : N.Inputs) :
  R.v37049 (state s) (inputs i) = Zmod.unsigned (N.v37049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37049 s i)) at 1.
  unfold R.v37049, N.v37049.
  unfold R.v6, N.v6.
  rewrite ?node_15825.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37050 (s : N.State) (i : N.Inputs) :
  R.v37050 (state s) (inputs i) = Zmod.unsigned (N.v37050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37050 s i)) at 1.
  unfold R.v37050, N.v37050.
  unfold R.v6, N.v6.
  rewrite ?node_15837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37051 (s : N.State) (i : N.Inputs) :
  R.v37051 (state s) (inputs i) = Zmod.unsigned (N.v37051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37051 s i)) at 1.
  unfold R.v37051, N.v37051.
  rewrite ?node_37048.
  rewrite ?node_37049.
  rewrite ?node_37050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37052 (s : N.State) (i : N.Inputs) :
  R.v37052 (state s) (inputs i) = Zmod.unsigned (N.v37052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37052 s i)) at 1.
  unfold R.v37052, N.v37052.
  rewrite ?node_37047.
  rewrite ?node_37051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37053 (s : N.State) (i : N.Inputs) :
  R.v37053 (state s) (inputs i) = Zmod.unsigned (N.v37053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37053 s i)) at 1.
  unfold R.v37053, N.v37053.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37054 (s : N.State) (i : N.Inputs) :
  R.v37054 (state s) (inputs i) = Zmod.unsigned (N.v37054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37054 s i)) at 1.
  unfold R.v37054, N.v37054.
  unfold R.v16463, N.v16463.
  rewrite !state_r2208_nr_5F2232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2208_nr_5F2232 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37055 (s : N.State) (i : N.Inputs) :
  R.v37055 (state s) (inputs i) = Zmod.unsigned (N.v37055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37055 s i)) at 1.
  unfold R.v37055, N.v37055.
  unfold R.v6, N.v6.
  rewrite !state_r2207_nr_5F2231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2207_nr_5F2231 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37056 (s : N.State) (i : N.Inputs) :
  R.v37056 (state s) (inputs i) = Zmod.unsigned (N.v37056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37056 s i)) at 1.
  unfold R.v37056, N.v37056.
  unfold R.v19, N.v19.
  rewrite ?node_37055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37057 (s : N.State) (i : N.Inputs) :
  R.v37057 (state s) (inputs i) = Zmod.unsigned (N.v37057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37057 s i)) at 1.
  unfold R.v37057, N.v37057.
  unfold R.v16484, N.v16484.
  rewrite ?node_37056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37058 (s : N.State) (i : N.Inputs) :
  R.v37058 (state s) (inputs i) = Zmod.unsigned (N.v37058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37058 s i)) at 1.
  unfold R.v37058, N.v37058.
  rewrite ?node_37054.
  rewrite ?node_37057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37059 (s : N.State) (i : N.Inputs) :
  R.v37059 (state s) (inputs i) = Zmod.unsigned (N.v37059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37059 s i)) at 1.
  unfold R.v37059, N.v37059.
  unfold R.v6, N.v6.
  rewrite ?node_37058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37060 (s : N.State) (i : N.Inputs) :
  R.v37060 (state s) (inputs i) = Zmod.unsigned (N.v37060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37060 s i)) at 1.
  unfold R.v37060, N.v37060.
  rewrite ?node_15775.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37061 (s : N.State) (i : N.Inputs) :
  R.v37061 (state s) (inputs i) = Zmod.unsigned (N.v37061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37061 s i)) at 1.
  unfold R.v37061, N.v37061.
  unfold R.v6, N.v6.
  rewrite ?node_15825.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37062 (s : N.State) (i : N.Inputs) :
  R.v37062 (state s) (inputs i) = Zmod.unsigned (N.v37062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37062 s i)) at 1.
  unfold R.v37062, N.v37062.
  rewrite ?node_37060.
  rewrite ?node_37061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37063 (s : N.State) (i : N.Inputs) :
  R.v37063 (state s) (inputs i) = Zmod.unsigned (N.v37063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37063 s i)) at 1.
  unfold R.v37063, N.v37063.
  rewrite ?node_37059.
  rewrite ?node_37062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37064 (s : N.State) (i : N.Inputs) :
  R.v37064 (state s) (inputs i) = Zmod.unsigned (N.v37064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37064 s i)) at 1.
  unfold R.v37064, N.v37064.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37065 (s : N.State) (i : N.Inputs) :
  R.v37065 (state s) (inputs i) = Zmod.unsigned (N.v37065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37065 s i)) at 1.
  unfold R.v37065, N.v37065.
  rewrite ?node_15779.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37066 (s : N.State) (i : N.Inputs) :
  R.v37066 (state s) (inputs i) = Zmod.unsigned (N.v37066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37066 s i)) at 1.
  unfold R.v37066, N.v37066.
  unfold R.v6, N.v6.
  rewrite !state_r2209_nr_5F2233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2209_nr_5F2233 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37067 (s : N.State) (i : N.Inputs) :
  R.v37067 (state s) (inputs i) = Zmod.unsigned (N.v37067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37067 s i)) at 1.
  unfold R.v37067, N.v37067.
  unfold R.v6, N.v6.
  rewrite ?node_15775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37068 (s : N.State) (i : N.Inputs) :
  R.v37068 (state s) (inputs i) = Zmod.unsigned (N.v37068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37068 s i)) at 1.
  unfold R.v37068, N.v37068.
  rewrite ?node_37066.
  rewrite ?node_37067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37069 (s : N.State) (i : N.Inputs) :
  R.v37069 (state s) (inputs i) = Zmod.unsigned (N.v37069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37069 s i)) at 1.
  unfold R.v37069, N.v37069.
  unfold R.v16484, N.v16484.
  rewrite ?node_37068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37070 (s : N.State) (i : N.Inputs) :
  R.v37070 (state s) (inputs i) = Zmod.unsigned (N.v37070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37070 s i)) at 1.
  unfold R.v37070, N.v37070.
  rewrite ?node_37065.
  rewrite ?node_37069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37071 (s : N.State) (i : N.Inputs) :
  R.v37071 (state s) (inputs i) = Zmod.unsigned (N.v37071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37071 s i)) at 1.
  unfold R.v37071, N.v37071.
  unfold R.v6, N.v6.
  rewrite ?node_37070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37072 (s : N.State) (i : N.Inputs) :
  R.v37072 (state s) (inputs i) = Zmod.unsigned (N.v37072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37072 s i)) at 1.
  unfold R.v37072, N.v37072.
  rewrite ?node_15780.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37073 (s : N.State) (i : N.Inputs) :
  R.v37073 (state s) (inputs i) = Zmod.unsigned (N.v37073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37073 s i)) at 1.
  unfold R.v37073, N.v37073.
  unfold R.v6, N.v6.
  rewrite ?node_15837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37074 (s : N.State) (i : N.Inputs) :
  R.v37074 (state s) (inputs i) = Zmod.unsigned (N.v37074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37074 s i)) at 1.
  unfold R.v37074, N.v37074.
  rewrite ?node_37072.
  rewrite ?node_37073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37075 (s : N.State) (i : N.Inputs) :
  R.v37075 (state s) (inputs i) = Zmod.unsigned (N.v37075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37075 s i)) at 1.
  unfold R.v37075, N.v37075.
  rewrite ?node_37071.
  rewrite ?node_37074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37076 (s : N.State) (i : N.Inputs) :
  R.v37076 (state s) (inputs i) = Zmod.unsigned (N.v37076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37076 s i)) at 1.
  unfold R.v37076, N.v37076.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37077 (s : N.State) (i : N.Inputs) :
  R.v37077 (state s) (inputs i) = Zmod.unsigned (N.v37077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37077 s i)) at 1.
  unfold R.v37077, N.v37077.
  rewrite ?node_15786.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37078 (s : N.State) (i : N.Inputs) :
  R.v37078 (state s) (inputs i) = Zmod.unsigned (N.v37078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37078 s i)) at 1.
  unfold R.v37078, N.v37078.
  unfold R.v16463, N.v16463.
  rewrite !state_r2213_nr_5F2237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2213_nr_5F2237 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37079 (s : N.State) (i : N.Inputs) :
  R.v37079 (state s) (inputs i) = Zmod.unsigned (N.v37079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37079 s i)) at 1.
  unfold R.v37079, N.v37079.
  unfold R.v16463, N.v16463.
  rewrite !state_r2212_nr_5F2236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2212_nr_5F2236 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37080 (s : N.State) (i : N.Inputs) :
  R.v37080 (state s) (inputs i) = Zmod.unsigned (N.v37080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37080 s i)) at 1.
  unfold R.v37080, N.v37080.
  unfold R.v6, N.v6.
  rewrite !state_r2211_nr_5F2235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2211_nr_5F2235 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37081 (s : N.State) (i : N.Inputs) :
  R.v37081 (state s) (inputs i) = Zmod.unsigned (N.v37081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37081 s i)) at 1.
  unfold R.v37081, N.v37081.
  unfold R.v6, N.v6.
  rewrite !state_r2210_nr_5F2234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2210_nr_5F2234 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37082 (s : N.State) (i : N.Inputs) :
  R.v37082 (state s) (inputs i) = Zmod.unsigned (N.v37082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37082 s i)) at 1.
  unfold R.v37082, N.v37082.
  rewrite ?node_37080.
  rewrite ?node_37081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37083 (s : N.State) (i : N.Inputs) :
  R.v37083 (state s) (inputs i) = Zmod.unsigned (N.v37083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37083 s i)) at 1.
  unfold R.v37083, N.v37083.
  unfold R.v16484, N.v16484.
  rewrite ?node_37082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37084 (s : N.State) (i : N.Inputs) :
  R.v37084 (state s) (inputs i) = Zmod.unsigned (N.v37084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37084 s i)) at 1.
  unfold R.v37084, N.v37084.
  rewrite ?node_37077.
  rewrite ?node_37078.
  rewrite ?node_37079.
  rewrite ?node_37083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37085 (s : N.State) (i : N.Inputs) :
  R.v37085 (state s) (inputs i) = Zmod.unsigned (N.v37085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37085 s i)) at 1.
  unfold R.v37085, N.v37085.
  unfold R.v6, N.v6.
  rewrite ?node_37084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37086 (s : N.State) (i : N.Inputs) :
  R.v37086 (state s) (inputs i) = Zmod.unsigned (N.v37086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37086 s i)) at 1.
  unfold R.v37086, N.v37086.
  rewrite ?node_15787.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37087 (s : N.State) (i : N.Inputs) :
  R.v37087 (state s) (inputs i) = Zmod.unsigned (N.v37087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37087 s i)) at 1.
  unfold R.v37087, N.v37087.
  unfold R.v6, N.v6.
  rewrite ?node_15832.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37088 (s : N.State) (i : N.Inputs) :
  R.v37088 (state s) (inputs i) = Zmod.unsigned (N.v37088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37088 s i)) at 1.
  unfold R.v37088, N.v37088.
  unfold R.v6, N.v6.
  rewrite ?node_15841.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37089 (s : N.State) (i : N.Inputs) :
  R.v37089 (state s) (inputs i) = Zmod.unsigned (N.v37089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37089 s i)) at 1.
  unfold R.v37089, N.v37089.
  rewrite ?node_37086.
  rewrite ?node_37087.
  rewrite ?node_37088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37090 (s : N.State) (i : N.Inputs) :
  R.v37090 (state s) (inputs i) = Zmod.unsigned (N.v37090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37090 s i)) at 1.
  unfold R.v37090, N.v37090.
  rewrite ?node_37085.
  rewrite ?node_37089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37091 (s : N.State) (i : N.Inputs) :
  R.v37091 (state s) (inputs i) = Zmod.unsigned (N.v37091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37091 s i)) at 1.
  unfold R.v37091, N.v37091.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37092 (s : N.State) (i : N.Inputs) :
  R.v37092 (state s) (inputs i) = Zmod.unsigned (N.v37092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37092 s i)) at 1.
  unfold R.v37092, N.v37092.
  unfold R.v16463, N.v16463.
  rewrite !state_r2212_nr_5F2236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2212_nr_5F2236 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37093 (s : N.State) (i : N.Inputs) :
  R.v37093 (state s) (inputs i) = Zmod.unsigned (N.v37093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37093 s i)) at 1.
  unfold R.v37093, N.v37093.
  unfold R.v6, N.v6.
  rewrite !state_r2211_nr_5F2235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2211_nr_5F2235 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37094 (s : N.State) (i : N.Inputs) :
  R.v37094 (state s) (inputs i) = Zmod.unsigned (N.v37094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37094 s i)) at 1.
  unfold R.v37094, N.v37094.
  unfold R.v6, N.v6.
  rewrite !state_r2210_nr_5F2234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2210_nr_5F2234 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37095 (s : N.State) (i : N.Inputs) :
  R.v37095 (state s) (inputs i) = Zmod.unsigned (N.v37095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37095 s i)) at 1.
  unfold R.v37095, N.v37095.
  rewrite ?node_37093.
  rewrite ?node_37094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37096 (s : N.State) (i : N.Inputs) :
  R.v37096 (state s) (inputs i) = Zmod.unsigned (N.v37096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37096 s i)) at 1.
  unfold R.v37096, N.v37096.
  unfold R.v16484, N.v16484.
  rewrite ?node_37095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37097 (s : N.State) (i : N.Inputs) :
  R.v37097 (state s) (inputs i) = Zmod.unsigned (N.v37097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37097 s i)) at 1.
  unfold R.v37097, N.v37097.
  rewrite ?node_37092.
  rewrite ?node_37096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37098 (s : N.State) (i : N.Inputs) :
  R.v37098 (state s) (inputs i) = Zmod.unsigned (N.v37098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37098 s i)) at 1.
  unfold R.v37098, N.v37098.
  unfold R.v6, N.v6.
  rewrite ?node_37097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37099 (s : N.State) (i : N.Inputs) :
  R.v37099 (state s) (inputs i) = Zmod.unsigned (N.v37099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37099 s i)) at 1.
  unfold R.v37099, N.v37099.
  rewrite ?node_15782.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37100 (s : N.State) (i : N.Inputs) :
  R.v37100 (state s) (inputs i) = Zmod.unsigned (N.v37100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37100 s i)) at 1.
  unfold R.v37100, N.v37100.
  unfold R.v6, N.v6.
  rewrite ?node_15832.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37101 (s : N.State) (i : N.Inputs) :
  R.v37101 (state s) (inputs i) = Zmod.unsigned (N.v37101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37101 s i)) at 1.
  unfold R.v37101, N.v37101.
  rewrite ?node_37099.
  rewrite ?node_37100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37102 (s : N.State) (i : N.Inputs) :
  R.v37102 (state s) (inputs i) = Zmod.unsigned (N.v37102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37102 s i)) at 1.
  unfold R.v37102, N.v37102.
  rewrite ?node_37098.
  rewrite ?node_37101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37103 (s : N.State) (i : N.Inputs) :
  R.v37103 (state s) (inputs i) = Zmod.unsigned (N.v37103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37103 s i)) at 1.
  unfold R.v37103, N.v37103.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37104 (s : N.State) (i : N.Inputs) :
  R.v37104 (state s) (inputs i) = Zmod.unsigned (N.v37104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37104 s i)) at 1.
  unfold R.v37104, N.v37104.
  rewrite ?node_15786.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37105 (s : N.State) (i : N.Inputs) :
  R.v37105 (state s) (inputs i) = Zmod.unsigned (N.v37105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37105 s i)) at 1.
  unfold R.v37105, N.v37105.
  unfold R.v6, N.v6.
  rewrite !state_r2213_nr_5F2237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2213_nr_5F2237 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37106 (s : N.State) (i : N.Inputs) :
  R.v37106 (state s) (inputs i) = Zmod.unsigned (N.v37106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37106 s i)) at 1.
  unfold R.v37106, N.v37106.
  unfold R.v6, N.v6.
  rewrite ?node_15782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37107 (s : N.State) (i : N.Inputs) :
  R.v37107 (state s) (inputs i) = Zmod.unsigned (N.v37107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37107 s i)) at 1.
  unfold R.v37107, N.v37107.
  rewrite ?node_37105.
  rewrite ?node_37106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37108 (s : N.State) (i : N.Inputs) :
  R.v37108 (state s) (inputs i) = Zmod.unsigned (N.v37108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37108 s i)) at 1.
  unfold R.v37108, N.v37108.
  unfold R.v16484, N.v16484.
  rewrite ?node_37107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37109 (s : N.State) (i : N.Inputs) :
  R.v37109 (state s) (inputs i) = Zmod.unsigned (N.v37109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37109 s i)) at 1.
  unfold R.v37109, N.v37109.
  rewrite ?node_37104.
  rewrite ?node_37108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37110 (s : N.State) (i : N.Inputs) :
  R.v37110 (state s) (inputs i) = Zmod.unsigned (N.v37110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37110 s i)) at 1.
  unfold R.v37110, N.v37110.
  unfold R.v6, N.v6.
  rewrite ?node_37109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37111 (s : N.State) (i : N.Inputs) :
  R.v37111 (state s) (inputs i) = Zmod.unsigned (N.v37111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37111 s i)) at 1.
  unfold R.v37111, N.v37111.
  rewrite ?node_15787.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37112 (s : N.State) (i : N.Inputs) :
  R.v37112 (state s) (inputs i) = Zmod.unsigned (N.v37112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37112 s i)) at 1.
  unfold R.v37112, N.v37112.
  unfold R.v6, N.v6.
  rewrite ?node_15841.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37113 (s : N.State) (i : N.Inputs) :
  R.v37113 (state s) (inputs i) = Zmod.unsigned (N.v37113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37113 s i)) at 1.
  unfold R.v37113, N.v37113.
  rewrite ?node_37111.
  rewrite ?node_37112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37114 (s : N.State) (i : N.Inputs) :
  R.v37114 (state s) (inputs i) = Zmod.unsigned (N.v37114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37114 s i)) at 1.
  unfold R.v37114, N.v37114.
  rewrite ?node_37110.
  rewrite ?node_37113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37115 (s : N.State) (i : N.Inputs) :
  R.v37115 (state s) (inputs i) = Zmod.unsigned (N.v37115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37115 s i)) at 1.
  unfold R.v37115, N.v37115.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37116 (s : N.State) (i : N.Inputs) :
  R.v37116 (state s) (inputs i) = Zmod.unsigned (N.v37116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37116 s i)) at 1.
  unfold R.v37116, N.v37116.
  rewrite ?node_15825.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37117 (s : N.State) (i : N.Inputs) :
  R.v37117 (state s) (inputs i) = Zmod.unsigned (N.v37117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37117 s i)) at 1.
  unfold R.v37117, N.v37117.
  unfold R.v16463, N.v16463.
  rewrite !state_r2218_nr_5F2242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2218_nr_5F2242 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37118 (s : N.State) (i : N.Inputs) :
  R.v37118 (state s) (inputs i) = Zmod.unsigned (N.v37118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37118 s i)) at 1.
  unfold R.v37118, N.v37118.
  unfold R.v16463, N.v16463.
  rewrite !state_r2217_nr_5F2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2217_nr_5F2241 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37119 (s : N.State) (i : N.Inputs) :
  R.v37119 (state s) (inputs i) = Zmod.unsigned (N.v37119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37119 s i)) at 1.
  unfold R.v37119, N.v37119.
  unfold R.v6, N.v6.
  rewrite !state_r2216_nr_5F2240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2216_nr_5F2240 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37120 (s : N.State) (i : N.Inputs) :
  R.v37120 (state s) (inputs i) = Zmod.unsigned (N.v37120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37120 s i)) at 1.
  unfold R.v37120, N.v37120.
  unfold R.v6, N.v6.
  rewrite !state_r2215_nr_5F2239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2215_nr_5F2239 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37121 (s : N.State) (i : N.Inputs) :
  R.v37121 (state s) (inputs i) = Zmod.unsigned (N.v37121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37121 s i)) at 1.
  unfold R.v37121, N.v37121.
  rewrite ?node_37119.
  rewrite ?node_37120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37122 (s : N.State) (i : N.Inputs) :
  R.v37122 (state s) (inputs i) = Zmod.unsigned (N.v37122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37122 s i)) at 1.
  unfold R.v37122, N.v37122.
  unfold R.v16484, N.v16484.
  rewrite ?node_37121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37123 (s : N.State) (i : N.Inputs) :
  R.v37123 (state s) (inputs i) = Zmod.unsigned (N.v37123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37123 s i)) at 1.
  unfold R.v37123, N.v37123.
  rewrite ?node_37116.
  rewrite ?node_37117.
  rewrite ?node_37118.
  rewrite ?node_37122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37124 (s : N.State) (i : N.Inputs) :
  R.v37124 (state s) (inputs i) = Zmod.unsigned (N.v37124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37124 s i)) at 1.
  unfold R.v37124, N.v37124.
  unfold R.v6, N.v6.
  rewrite ?node_37123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37125 (s : N.State) (i : N.Inputs) :
  R.v37125 (state s) (inputs i) = Zmod.unsigned (N.v37125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37125 s i)) at 1.
  unfold R.v37125, N.v37125.
  rewrite ?node_15826.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37126 (s : N.State) (i : N.Inputs) :
  R.v37126 (state s) (inputs i) = Zmod.unsigned (N.v37126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37126 s i)) at 1.
  unfold R.v37126, N.v37126.
  unfold R.v6, N.v6.
  rewrite ?node_15869.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37127 (s : N.State) (i : N.Inputs) :
  R.v37127 (state s) (inputs i) = Zmod.unsigned (N.v37127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37127 s i)) at 1.
  unfold R.v37127, N.v37127.
  unfold R.v6, N.v6.
  rewrite ?node_15881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37128 (s : N.State) (i : N.Inputs) :
  R.v37128 (state s) (inputs i) = Zmod.unsigned (N.v37128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37128 s i)) at 1.
  unfold R.v37128, N.v37128.
  rewrite ?node_37125.
  rewrite ?node_37126.
  rewrite ?node_37127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37129 (s : N.State) (i : N.Inputs) :
  R.v37129 (state s) (inputs i) = Zmod.unsigned (N.v37129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37129 s i)) at 1.
  unfold R.v37129, N.v37129.
  rewrite ?node_37124.
  rewrite ?node_37128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37130 (s : N.State) (i : N.Inputs) :
  R.v37130 (state s) (inputs i) = Zmod.unsigned (N.v37130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37130 s i)) at 1.
  unfold R.v37130, N.v37130.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37131 (s : N.State) (i : N.Inputs) :
  R.v37131 (state s) (inputs i) = Zmod.unsigned (N.v37131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37131 s i)) at 1.
  unfold R.v37131, N.v37131.
  unfold R.v16463, N.v16463.
  rewrite !state_r2217_nr_5F2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2217_nr_5F2241 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37132 (s : N.State) (i : N.Inputs) :
  R.v37132 (state s) (inputs i) = Zmod.unsigned (N.v37132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37132 s i)) at 1.
  unfold R.v37132, N.v37132.
  unfold R.v6, N.v6.
  rewrite !state_r2216_nr_5F2240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2216_nr_5F2240 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37133 (s : N.State) (i : N.Inputs) :
  R.v37133 (state s) (inputs i) = Zmod.unsigned (N.v37133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37133 s i)) at 1.
  unfold R.v37133, N.v37133.
  unfold R.v6, N.v6.
  rewrite !state_r2215_nr_5F2239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2215_nr_5F2239 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37134 (s : N.State) (i : N.Inputs) :
  R.v37134 (state s) (inputs i) = Zmod.unsigned (N.v37134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37134 s i)) at 1.
  unfold R.v37134, N.v37134.
  rewrite ?node_37132.
  rewrite ?node_37133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37135 (s : N.State) (i : N.Inputs) :
  R.v37135 (state s) (inputs i) = Zmod.unsigned (N.v37135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37135 s i)) at 1.
  unfold R.v37135, N.v37135.
  unfold R.v16484, N.v16484.
  rewrite ?node_37134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37136 (s : N.State) (i : N.Inputs) :
  R.v37136 (state s) (inputs i) = Zmod.unsigned (N.v37136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37136 s i)) at 1.
  unfold R.v37136, N.v37136.
  rewrite ?node_37131.
  rewrite ?node_37135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37137 (s : N.State) (i : N.Inputs) :
  R.v37137 (state s) (inputs i) = Zmod.unsigned (N.v37137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37137 s i)) at 1.
  unfold R.v37137, N.v37137.
  unfold R.v6, N.v6.
  rewrite ?node_37136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37138 (s : N.State) (i : N.Inputs) :
  R.v37138 (state s) (inputs i) = Zmod.unsigned (N.v37138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37138 s i)) at 1.
  unfold R.v37138, N.v37138.
  rewrite ?node_15822.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37139 (s : N.State) (i : N.Inputs) :
  R.v37139 (state s) (inputs i) = Zmod.unsigned (N.v37139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37139 s i)) at 1.
  unfold R.v37139, N.v37139.
  unfold R.v6, N.v6.
  rewrite ?node_15869.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37140 (s : N.State) (i : N.Inputs) :
  R.v37140 (state s) (inputs i) = Zmod.unsigned (N.v37140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37140 s i)) at 1.
  unfold R.v37140, N.v37140.
  rewrite ?node_37138.
  rewrite ?node_37139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37141 (s : N.State) (i : N.Inputs) :
  R.v37141 (state s) (inputs i) = Zmod.unsigned (N.v37141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37141 s i)) at 1.
  unfold R.v37141, N.v37141.
  rewrite ?node_37137.
  rewrite ?node_37140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37142 (s : N.State) (i : N.Inputs) :
  R.v37142 (state s) (inputs i) = Zmod.unsigned (N.v37142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37142 s i)) at 1.
  unfold R.v37142, N.v37142.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37143 (s : N.State) (i : N.Inputs) :
  R.v37143 (state s) (inputs i) = Zmod.unsigned (N.v37143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37143 s i)) at 1.
  unfold R.v37143, N.v37143.
  rewrite ?node_15825.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37144 (s : N.State) (i : N.Inputs) :
  R.v37144 (state s) (inputs i) = Zmod.unsigned (N.v37144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37144 s i)) at 1.
  unfold R.v37144, N.v37144.
  unfold R.v6, N.v6.
  rewrite !state_r2218_nr_5F2242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2218_nr_5F2242 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37145 (s : N.State) (i : N.Inputs) :
  R.v37145 (state s) (inputs i) = Zmod.unsigned (N.v37145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37145 s i)) at 1.
  unfold R.v37145, N.v37145.
  unfold R.v6, N.v6.
  rewrite ?node_15822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37146 (s : N.State) (i : N.Inputs) :
  R.v37146 (state s) (inputs i) = Zmod.unsigned (N.v37146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37146 s i)) at 1.
  unfold R.v37146, N.v37146.
  rewrite ?node_37144.
  rewrite ?node_37145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37147 (s : N.State) (i : N.Inputs) :
  R.v37147 (state s) (inputs i) = Zmod.unsigned (N.v37147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37147 s i)) at 1.
  unfold R.v37147, N.v37147.
  unfold R.v16484, N.v16484.
  rewrite ?node_37146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37148 (s : N.State) (i : N.Inputs) :
  R.v37148 (state s) (inputs i) = Zmod.unsigned (N.v37148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37148 s i)) at 1.
  unfold R.v37148, N.v37148.
  rewrite ?node_37143.
  rewrite ?node_37147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37149 (s : N.State) (i : N.Inputs) :
  R.v37149 (state s) (inputs i) = Zmod.unsigned (N.v37149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37149 s i)) at 1.
  unfold R.v37149, N.v37149.
  unfold R.v6, N.v6.
  rewrite ?node_37148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37150 (s : N.State) (i : N.Inputs) :
  R.v37150 (state s) (inputs i) = Zmod.unsigned (N.v37150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37150 s i)) at 1.
  unfold R.v37150, N.v37150.
  rewrite ?node_15826.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37151 (s : N.State) (i : N.Inputs) :
  R.v37151 (state s) (inputs i) = Zmod.unsigned (N.v37151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37151 s i)) at 1.
  unfold R.v37151, N.v37151.
  unfold R.v6, N.v6.
  rewrite ?node_15881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37152 (s : N.State) (i : N.Inputs) :
  R.v37152 (state s) (inputs i) = Zmod.unsigned (N.v37152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37152 s i)) at 1.
  unfold R.v37152, N.v37152.
  rewrite ?node_37150.
  rewrite ?node_37151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37153 (s : N.State) (i : N.Inputs) :
  R.v37153 (state s) (inputs i) = Zmod.unsigned (N.v37153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37153 s i)) at 1.
  unfold R.v37153, N.v37153.
  rewrite ?node_37149.
  rewrite ?node_37152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37154 (s : N.State) (i : N.Inputs) :
  R.v37154 (state s) (inputs i) = Zmod.unsigned (N.v37154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37154 s i)) at 1.
  unfold R.v37154, N.v37154.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37155 (s : N.State) (i : N.Inputs) :
  R.v37155 (state s) (inputs i) = Zmod.unsigned (N.v37155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37155 s i)) at 1.
  unfold R.v37155, N.v37155.
  rewrite ?node_15832.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37156 (s : N.State) (i : N.Inputs) :
  R.v37156 (state s) (inputs i) = Zmod.unsigned (N.v37156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37156 s i)) at 1.
  unfold R.v37156, N.v37156.
  unfold R.v16463, N.v16463.
  rewrite !state_r2222_nr_5F2246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2222_nr_5F2246 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37157 (s : N.State) (i : N.Inputs) :
  R.v37157 (state s) (inputs i) = Zmod.unsigned (N.v37157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37157 s i)) at 1.
  unfold R.v37157, N.v37157.
  unfold R.v16463, N.v16463.
  rewrite !state_r2221_nr_5F2245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2221_nr_5F2245 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37158 (s : N.State) (i : N.Inputs) :
  R.v37158 (state s) (inputs i) = Zmod.unsigned (N.v37158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37158 s i)) at 1.
  unfold R.v37158, N.v37158.
  unfold R.v6, N.v6.
  rewrite !state_r2220_nr_5F2244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2220_nr_5F2244 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37159 (s : N.State) (i : N.Inputs) :
  R.v37159 (state s) (inputs i) = Zmod.unsigned (N.v37159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37159 s i)) at 1.
  unfold R.v37159, N.v37159.
  unfold R.v6, N.v6.
  rewrite !state_r2219_nr_5F2243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2219_nr_5F2243 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37160 (s : N.State) (i : N.Inputs) :
  R.v37160 (state s) (inputs i) = Zmod.unsigned (N.v37160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37160 s i)) at 1.
  unfold R.v37160, N.v37160.
  rewrite ?node_37158.
  rewrite ?node_37159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37161 (s : N.State) (i : N.Inputs) :
  R.v37161 (state s) (inputs i) = Zmod.unsigned (N.v37161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37161 s i)) at 1.
  unfold R.v37161, N.v37161.
  unfold R.v16484, N.v16484.
  rewrite ?node_37160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37162 (s : N.State) (i : N.Inputs) :
  R.v37162 (state s) (inputs i) = Zmod.unsigned (N.v37162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37162 s i)) at 1.
  unfold R.v37162, N.v37162.
  rewrite ?node_37155.
  rewrite ?node_37156.
  rewrite ?node_37157.
  rewrite ?node_37161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37163 (s : N.State) (i : N.Inputs) :
  R.v37163 (state s) (inputs i) = Zmod.unsigned (N.v37163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37163 s i)) at 1.
  unfold R.v37163, N.v37163.
  unfold R.v6, N.v6.
  rewrite ?node_37162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37164 (s : N.State) (i : N.Inputs) :
  R.v37164 (state s) (inputs i) = Zmod.unsigned (N.v37164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37164 s i)) at 1.
  unfold R.v37164, N.v37164.
  rewrite ?node_15833.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37165 (s : N.State) (i : N.Inputs) :
  R.v37165 (state s) (inputs i) = Zmod.unsigned (N.v37165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37165 s i)) at 1.
  unfold R.v37165, N.v37165.
  unfold R.v6, N.v6.
  rewrite ?node_15876.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37166 (s : N.State) (i : N.Inputs) :
  R.v37166 (state s) (inputs i) = Zmod.unsigned (N.v37166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37166 s i)) at 1.
  unfold R.v37166, N.v37166.
  unfold R.v6, N.v6.
  rewrite ?node_15885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37167 (s : N.State) (i : N.Inputs) :
  R.v37167 (state s) (inputs i) = Zmod.unsigned (N.v37167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37167 s i)) at 1.
  unfold R.v37167, N.v37167.
  rewrite ?node_37164.
  rewrite ?node_37165.
  rewrite ?node_37166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37168 (s : N.State) (i : N.Inputs) :
  R.v37168 (state s) (inputs i) = Zmod.unsigned (N.v37168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37168 s i)) at 1.
  unfold R.v37168, N.v37168.
  rewrite ?node_37163.
  rewrite ?node_37167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37169 (s : N.State) (i : N.Inputs) :
  R.v37169 (state s) (inputs i) = Zmod.unsigned (N.v37169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37169 s i)) at 1.
  unfold R.v37169, N.v37169.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37170 (s : N.State) (i : N.Inputs) :
  R.v37170 (state s) (inputs i) = Zmod.unsigned (N.v37170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37170 s i)) at 1.
  unfold R.v37170, N.v37170.
  unfold R.v16463, N.v16463.
  rewrite !state_r2221_nr_5F2245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2221_nr_5F2245 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37171 (s : N.State) (i : N.Inputs) :
  R.v37171 (state s) (inputs i) = Zmod.unsigned (N.v37171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37171 s i)) at 1.
  unfold R.v37171, N.v37171.
  unfold R.v6, N.v6.
  rewrite !state_r2220_nr_5F2244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2220_nr_5F2244 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37172 (s : N.State) (i : N.Inputs) :
  R.v37172 (state s) (inputs i) = Zmod.unsigned (N.v37172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37172 s i)) at 1.
  unfold R.v37172, N.v37172.
  unfold R.v6, N.v6.
  rewrite !state_r2219_nr_5F2243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2219_nr_5F2243 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37173 (s : N.State) (i : N.Inputs) :
  R.v37173 (state s) (inputs i) = Zmod.unsigned (N.v37173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37173 s i)) at 1.
  unfold R.v37173, N.v37173.
  rewrite ?node_37171.
  rewrite ?node_37172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37174 (s : N.State) (i : N.Inputs) :
  R.v37174 (state s) (inputs i) = Zmod.unsigned (N.v37174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37174 s i)) at 1.
  unfold R.v37174, N.v37174.
  unfold R.v16484, N.v16484.
  rewrite ?node_37173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37175 (s : N.State) (i : N.Inputs) :
  R.v37175 (state s) (inputs i) = Zmod.unsigned (N.v37175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37175 s i)) at 1.
  unfold R.v37175, N.v37175.
  rewrite ?node_37170.
  rewrite ?node_37174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37176 (s : N.State) (i : N.Inputs) :
  R.v37176 (state s) (inputs i) = Zmod.unsigned (N.v37176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37176 s i)) at 1.
  unfold R.v37176, N.v37176.
  unfold R.v6, N.v6.
  rewrite ?node_37175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37177 (s : N.State) (i : N.Inputs) :
  R.v37177 (state s) (inputs i) = Zmod.unsigned (N.v37177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37177 s i)) at 1.
  unfold R.v37177, N.v37177.
  rewrite ?node_15828.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37178 (s : N.State) (i : N.Inputs) :
  R.v37178 (state s) (inputs i) = Zmod.unsigned (N.v37178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37178 s i)) at 1.
  unfold R.v37178, N.v37178.
  unfold R.v6, N.v6.
  rewrite ?node_15876.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37179 (s : N.State) (i : N.Inputs) :
  R.v37179 (state s) (inputs i) = Zmod.unsigned (N.v37179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37179 s i)) at 1.
  unfold R.v37179, N.v37179.
  rewrite ?node_37177.
  rewrite ?node_37178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37180 (s : N.State) (i : N.Inputs) :
  R.v37180 (state s) (inputs i) = Zmod.unsigned (N.v37180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37180 s i)) at 1.
  unfold R.v37180, N.v37180.
  rewrite ?node_37176.
  rewrite ?node_37179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37181 (s : N.State) (i : N.Inputs) :
  R.v37181 (state s) (inputs i) = Zmod.unsigned (N.v37181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37181 s i)) at 1.
  unfold R.v37181, N.v37181.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37182 (s : N.State) (i : N.Inputs) :
  R.v37182 (state s) (inputs i) = Zmod.unsigned (N.v37182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37182 s i)) at 1.
  unfold R.v37182, N.v37182.
  rewrite ?node_15832.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37183 (s : N.State) (i : N.Inputs) :
  R.v37183 (state s) (inputs i) = Zmod.unsigned (N.v37183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37183 s i)) at 1.
  unfold R.v37183, N.v37183.
  unfold R.v6, N.v6.
  rewrite !state_r2222_nr_5F2246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2222_nr_5F2246 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37184 (s : N.State) (i : N.Inputs) :
  R.v37184 (state s) (inputs i) = Zmod.unsigned (N.v37184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37184 s i)) at 1.
  unfold R.v37184, N.v37184.
  unfold R.v6, N.v6.
  rewrite ?node_15828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37185 (s : N.State) (i : N.Inputs) :
  R.v37185 (state s) (inputs i) = Zmod.unsigned (N.v37185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37185 s i)) at 1.
  unfold R.v37185, N.v37185.
  rewrite ?node_37183.
  rewrite ?node_37184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37186 (s : N.State) (i : N.Inputs) :
  R.v37186 (state s) (inputs i) = Zmod.unsigned (N.v37186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37186 s i)) at 1.
  unfold R.v37186, N.v37186.
  unfold R.v16484, N.v16484.
  rewrite ?node_37185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37187 (s : N.State) (i : N.Inputs) :
  R.v37187 (state s) (inputs i) = Zmod.unsigned (N.v37187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37187 s i)) at 1.
  unfold R.v37187, N.v37187.
  rewrite ?node_37182.
  rewrite ?node_37186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37188 (s : N.State) (i : N.Inputs) :
  R.v37188 (state s) (inputs i) = Zmod.unsigned (N.v37188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37188 s i)) at 1.
  unfold R.v37188, N.v37188.
  unfold R.v6, N.v6.
  rewrite ?node_37187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37189 (s : N.State) (i : N.Inputs) :
  R.v37189 (state s) (inputs i) = Zmod.unsigned (N.v37189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37189 s i)) at 1.
  unfold R.v37189, N.v37189.
  rewrite ?node_15833.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37190 (s : N.State) (i : N.Inputs) :
  R.v37190 (state s) (inputs i) = Zmod.unsigned (N.v37190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37190 s i)) at 1.
  unfold R.v37190, N.v37190.
  unfold R.v6, N.v6.
  rewrite ?node_15885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37191 (s : N.State) (i : N.Inputs) :
  R.v37191 (state s) (inputs i) = Zmod.unsigned (N.v37191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37191 s i)) at 1.
  unfold R.v37191, N.v37191.
  rewrite ?node_37189.
  rewrite ?node_37190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37192 (s : N.State) (i : N.Inputs) :
  R.v37192 (state s) (inputs i) = Zmod.unsigned (N.v37192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37192 s i)) at 1.
  unfold R.v37192, N.v37192.
  rewrite ?node_37188.
  rewrite ?node_37191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37193 (s : N.State) (i : N.Inputs) :
  R.v37193 (state s) (inputs i) = Zmod.unsigned (N.v37193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37193 s i)) at 1.
  unfold R.v37193, N.v37193.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37194 (s : N.State) (i : N.Inputs) :
  R.v37194 (state s) (inputs i) = Zmod.unsigned (N.v37194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37194 s i)) at 1.
  unfold R.v37194, N.v37194.
  rewrite ?node_15869.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37195 (s : N.State) (i : N.Inputs) :
  R.v37195 (state s) (inputs i) = Zmod.unsigned (N.v37195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37195 s i)) at 1.
  unfold R.v37195, N.v37195.
  unfold R.v16463, N.v16463.
  rewrite !state_r2225_nr_5F2250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2225_nr_5F2250 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37196 (s : N.State) (i : N.Inputs) :
  R.v37196 (state s) (inputs i) = Zmod.unsigned (N.v37196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37196 s i)) at 1.
  unfold R.v37196, N.v37196.
  unfold R.v16463, N.v16463.
  rewrite !state_r2224_nr_5F2249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2224_nr_5F2249 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37197 (s : N.State) (i : N.Inputs) :
  R.v37197 (state s) (inputs i) = Zmod.unsigned (N.v37197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37197 s i)) at 1.
  unfold R.v37197, N.v37197.
  unfold R.v6, N.v6.
  rewrite !state_r2223_nr_5F2248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2223_nr_5F2248 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37198 (s : N.State) (i : N.Inputs) :
  R.v37198 (state s) (inputs i) = Zmod.unsigned (N.v37198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37198 s i)) at 1.
  unfold R.v37198, N.v37198.
  unfold R.v19, N.v19.
  rewrite ?node_37197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37199 (s : N.State) (i : N.Inputs) :
  R.v37199 (state s) (inputs i) = Zmod.unsigned (N.v37199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37199 s i)) at 1.
  unfold R.v37199, N.v37199.
  unfold R.v16484, N.v16484.
  rewrite ?node_37198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37200 (s : N.State) (i : N.Inputs) :
  R.v37200 (state s) (inputs i) = Zmod.unsigned (N.v37200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37200 s i)) at 1.
  unfold R.v37200, N.v37200.
  rewrite ?node_37194.
  rewrite ?node_37195.
  rewrite ?node_37196.
  rewrite ?node_37199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37201 (s : N.State) (i : N.Inputs) :
  R.v37201 (state s) (inputs i) = Zmod.unsigned (N.v37201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37201 s i)) at 1.
  unfold R.v37201, N.v37201.
  unfold R.v6, N.v6.
  rewrite ?node_37200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37202 (s : N.State) (i : N.Inputs) :
  R.v37202 (state s) (inputs i) = Zmod.unsigned (N.v37202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37202 s i)) at 1.
  unfold R.v37202, N.v37202.
  rewrite ?node_15870.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37203 (s : N.State) (i : N.Inputs) :
  R.v37203 (state s) (inputs i) = Zmod.unsigned (N.v37203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37203 s i)) at 1.
  unfold R.v37203, N.v37203.
  unfold R.v6, N.v6.
  rewrite ?node_15908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37204 (s : N.State) (i : N.Inputs) :
  R.v37204 (state s) (inputs i) = Zmod.unsigned (N.v37204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37204 s i)) at 1.
  unfold R.v37204, N.v37204.
  unfold R.v6, N.v6.
  rewrite ?node_15919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37205 (s : N.State) (i : N.Inputs) :
  R.v37205 (state s) (inputs i) = Zmod.unsigned (N.v37205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37205 s i)) at 1.
  unfold R.v37205, N.v37205.
  rewrite ?node_37202.
  rewrite ?node_37203.
  rewrite ?node_37204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37206 (s : N.State) (i : N.Inputs) :
  R.v37206 (state s) (inputs i) = Zmod.unsigned (N.v37206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37206 s i)) at 1.
  unfold R.v37206, N.v37206.
  rewrite ?node_37201.
  rewrite ?node_37205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37207 (s : N.State) (i : N.Inputs) :
  R.v37207 (state s) (inputs i) = Zmod.unsigned (N.v37207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37207 s i)) at 1.
  unfold R.v37207, N.v37207.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37208 (s : N.State) (i : N.Inputs) :
  R.v37208 (state s) (inputs i) = Zmod.unsigned (N.v37208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37208 s i)) at 1.
  unfold R.v37208, N.v37208.
  unfold R.v16463, N.v16463.
  rewrite !state_r2224_nr_5F2249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2224_nr_5F2249 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37209 (s : N.State) (i : N.Inputs) :
  R.v37209 (state s) (inputs i) = Zmod.unsigned (N.v37209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37209 s i)) at 1.
  unfold R.v37209, N.v37209.
  unfold R.v6, N.v6.
  rewrite !state_r2223_nr_5F2248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2223_nr_5F2248 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37210 (s : N.State) (i : N.Inputs) :
  R.v37210 (state s) (inputs i) = Zmod.unsigned (N.v37210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37210 s i)) at 1.
  unfold R.v37210, N.v37210.
  unfold R.v19, N.v19.
  rewrite ?node_37209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37211 (s : N.State) (i : N.Inputs) :
  R.v37211 (state s) (inputs i) = Zmod.unsigned (N.v37211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37211 s i)) at 1.
  unfold R.v37211, N.v37211.
  unfold R.v16484, N.v16484.
  rewrite ?node_37210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37212 (s : N.State) (i : N.Inputs) :
  R.v37212 (state s) (inputs i) = Zmod.unsigned (N.v37212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37212 s i)) at 1.
  unfold R.v37212, N.v37212.
  rewrite ?node_37208.
  rewrite ?node_37211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37213 (s : N.State) (i : N.Inputs) :
  R.v37213 (state s) (inputs i) = Zmod.unsigned (N.v37213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37213 s i)) at 1.
  unfold R.v37213, N.v37213.
  unfold R.v6, N.v6.
  rewrite ?node_37212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37214 (s : N.State) (i : N.Inputs) :
  R.v37214 (state s) (inputs i) = Zmod.unsigned (N.v37214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37214 s i)) at 1.
  unfold R.v37214, N.v37214.
  rewrite ?node_15865.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37215 (s : N.State) (i : N.Inputs) :
  R.v37215 (state s) (inputs i) = Zmod.unsigned (N.v37215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37215 s i)) at 1.
  unfold R.v37215, N.v37215.
  unfold R.v6, N.v6.
  rewrite ?node_15908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37216 (s : N.State) (i : N.Inputs) :
  R.v37216 (state s) (inputs i) = Zmod.unsigned (N.v37216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37216 s i)) at 1.
  unfold R.v37216, N.v37216.
  rewrite ?node_37214.
  rewrite ?node_37215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37217 (s : N.State) (i : N.Inputs) :
  R.v37217 (state s) (inputs i) = Zmod.unsigned (N.v37217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37217 s i)) at 1.
  unfold R.v37217, N.v37217.
  rewrite ?node_37213.
  rewrite ?node_37216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37218 (s : N.State) (i : N.Inputs) :
  R.v37218 (state s) (inputs i) = Zmod.unsigned (N.v37218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37218 s i)) at 1.
  unfold R.v37218, N.v37218.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37219 (s : N.State) (i : N.Inputs) :
  R.v37219 (state s) (inputs i) = Zmod.unsigned (N.v37219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37219 s i)) at 1.
  unfold R.v37219, N.v37219.
  rewrite ?node_15869.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37220 (s : N.State) (i : N.Inputs) :
  R.v37220 (state s) (inputs i) = Zmod.unsigned (N.v37220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37220 s i)) at 1.
  unfold R.v37220, N.v37220.
  unfold R.v6, N.v6.
  rewrite !state_r2225_nr_5F2250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2225_nr_5F2250 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37221 (s : N.State) (i : N.Inputs) :
  R.v37221 (state s) (inputs i) = Zmod.unsigned (N.v37221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37221 s i)) at 1.
  unfold R.v37221, N.v37221.
  unfold R.v6, N.v6.
  rewrite ?node_15865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37222 (s : N.State) (i : N.Inputs) :
  R.v37222 (state s) (inputs i) = Zmod.unsigned (N.v37222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37222 s i)) at 1.
  unfold R.v37222, N.v37222.
  rewrite ?node_37220.
  rewrite ?node_37221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37223 (s : N.State) (i : N.Inputs) :
  R.v37223 (state s) (inputs i) = Zmod.unsigned (N.v37223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37223 s i)) at 1.
  unfold R.v37223, N.v37223.
  unfold R.v16484, N.v16484.
  rewrite ?node_37222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37224 (s : N.State) (i : N.Inputs) :
  R.v37224 (state s) (inputs i) = Zmod.unsigned (N.v37224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37224 s i)) at 1.
  unfold R.v37224, N.v37224.
  rewrite ?node_37219.
  rewrite ?node_37223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37225 (s : N.State) (i : N.Inputs) :
  R.v37225 (state s) (inputs i) = Zmod.unsigned (N.v37225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37225 s i)) at 1.
  unfold R.v37225, N.v37225.
  unfold R.v6, N.v6.
  rewrite ?node_37224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37226 (s : N.State) (i : N.Inputs) :
  R.v37226 (state s) (inputs i) = Zmod.unsigned (N.v37226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37226 s i)) at 1.
  unfold R.v37226, N.v37226.
  rewrite ?node_15870.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37227 (s : N.State) (i : N.Inputs) :
  R.v37227 (state s) (inputs i) = Zmod.unsigned (N.v37227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37227 s i)) at 1.
  unfold R.v37227, N.v37227.
  unfold R.v6, N.v6.
  rewrite ?node_15919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37228 (s : N.State) (i : N.Inputs) :
  R.v37228 (state s) (inputs i) = Zmod.unsigned (N.v37228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37228 s i)) at 1.
  unfold R.v37228, N.v37228.
  rewrite ?node_37226.
  rewrite ?node_37227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37229 (s : N.State) (i : N.Inputs) :
  R.v37229 (state s) (inputs i) = Zmod.unsigned (N.v37229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37229 s i)) at 1.
  unfold R.v37229, N.v37229.
  rewrite ?node_37225.
  rewrite ?node_37228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37230 (s : N.State) (i : N.Inputs) :
  R.v37230 (state s) (inputs i) = Zmod.unsigned (N.v37230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37230 s i)) at 1.
  unfold R.v37230, N.v37230.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37231 (s : N.State) (i : N.Inputs) :
  R.v37231 (state s) (inputs i) = Zmod.unsigned (N.v37231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37231 s i)) at 1.
  unfold R.v37231, N.v37231.
  rewrite ?node_15876.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37232 (s : N.State) (i : N.Inputs) :
  R.v37232 (state s) (inputs i) = Zmod.unsigned (N.v37232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37232 s i)) at 1.
  unfold R.v37232, N.v37232.
  unfold R.v16463, N.v16463.
  rewrite !state_r2229_nr_5F2254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2229_nr_5F2254 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37233 (s : N.State) (i : N.Inputs) :
  R.v37233 (state s) (inputs i) = Zmod.unsigned (N.v37233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37233 s i)) at 1.
  unfold R.v37233, N.v37233.
  unfold R.v16463, N.v16463.
  rewrite !state_r2228_nr_5F2253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2228_nr_5F2253 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37234 (s : N.State) (i : N.Inputs) :
  R.v37234 (state s) (inputs i) = Zmod.unsigned (N.v37234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37234 s i)) at 1.
  unfold R.v37234, N.v37234.
  unfold R.v6, N.v6.
  rewrite !state_r2227_nr_5F2252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2227_nr_5F2252 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37235 (s : N.State) (i : N.Inputs) :
  R.v37235 (state s) (inputs i) = Zmod.unsigned (N.v37235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37235 s i)) at 1.
  unfold R.v37235, N.v37235.
  unfold R.v6, N.v6.
  rewrite !state_r2226_nr_5F2251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2226_nr_5F2251 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37236 (s : N.State) (i : N.Inputs) :
  R.v37236 (state s) (inputs i) = Zmod.unsigned (N.v37236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37236 s i)) at 1.
  unfold R.v37236, N.v37236.
  rewrite ?node_37234.
  rewrite ?node_37235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37237 (s : N.State) (i : N.Inputs) :
  R.v37237 (state s) (inputs i) = Zmod.unsigned (N.v37237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37237 s i)) at 1.
  unfold R.v37237, N.v37237.
  unfold R.v16484, N.v16484.
  rewrite ?node_37236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37238 (s : N.State) (i : N.Inputs) :
  R.v37238 (state s) (inputs i) = Zmod.unsigned (N.v37238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37238 s i)) at 1.
  unfold R.v37238, N.v37238.
  rewrite ?node_37231.
  rewrite ?node_37232.
  rewrite ?node_37233.
  rewrite ?node_37237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37239 (s : N.State) (i : N.Inputs) :
  R.v37239 (state s) (inputs i) = Zmod.unsigned (N.v37239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37239 s i)) at 1.
  unfold R.v37239, N.v37239.
  unfold R.v6, N.v6.
  rewrite ?node_37238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37240 (s : N.State) (i : N.Inputs) :
  R.v37240 (state s) (inputs i) = Zmod.unsigned (N.v37240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37240 s i)) at 1.
  unfold R.v37240, N.v37240.
  rewrite ?node_15877.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37241 (s : N.State) (i : N.Inputs) :
  R.v37241 (state s) (inputs i) = Zmod.unsigned (N.v37241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37241 s i)) at 1.
  unfold R.v37241, N.v37241.
  unfold R.v6, N.v6.
  rewrite ?node_15915.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37242 (s : N.State) (i : N.Inputs) :
  R.v37242 (state s) (inputs i) = Zmod.unsigned (N.v37242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37242 s i)) at 1.
  unfold R.v37242, N.v37242.
  unfold R.v6, N.v6.
  rewrite ?node_15927.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37243 (s : N.State) (i : N.Inputs) :
  R.v37243 (state s) (inputs i) = Zmod.unsigned (N.v37243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37243 s i)) at 1.
  unfold R.v37243, N.v37243.
  rewrite ?node_37240.
  rewrite ?node_37241.
  rewrite ?node_37242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37244 (s : N.State) (i : N.Inputs) :
  R.v37244 (state s) (inputs i) = Zmod.unsigned (N.v37244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37244 s i)) at 1.
  unfold R.v37244, N.v37244.
  rewrite ?node_37239.
  rewrite ?node_37243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37245 (s : N.State) (i : N.Inputs) :
  R.v37245 (state s) (inputs i) = Zmod.unsigned (N.v37245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37245 s i)) at 1.
  unfold R.v37245, N.v37245.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37246 (s : N.State) (i : N.Inputs) :
  R.v37246 (state s) (inputs i) = Zmod.unsigned (N.v37246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37246 s i)) at 1.
  unfold R.v37246, N.v37246.
  unfold R.v16463, N.v16463.
  rewrite !state_r2228_nr_5F2253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2228_nr_5F2253 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37247 (s : N.State) (i : N.Inputs) :
  R.v37247 (state s) (inputs i) = Zmod.unsigned (N.v37247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37247 s i)) at 1.
  unfold R.v37247, N.v37247.
  unfold R.v6, N.v6.
  rewrite !state_r2227_nr_5F2252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2227_nr_5F2252 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37248 (s : N.State) (i : N.Inputs) :
  R.v37248 (state s) (inputs i) = Zmod.unsigned (N.v37248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37248 s i)) at 1.
  unfold R.v37248, N.v37248.
  unfold R.v6, N.v6.
  rewrite !state_r2226_nr_5F2251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2226_nr_5F2251 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37249 (s : N.State) (i : N.Inputs) :
  R.v37249 (state s) (inputs i) = Zmod.unsigned (N.v37249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37249 s i)) at 1.
  unfold R.v37249, N.v37249.
  rewrite ?node_37247.
  rewrite ?node_37248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37250 (s : N.State) (i : N.Inputs) :
  R.v37250 (state s) (inputs i) = Zmod.unsigned (N.v37250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37250 s i)) at 1.
  unfold R.v37250, N.v37250.
  unfold R.v16484, N.v16484.
  rewrite ?node_37249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37251 (s : N.State) (i : N.Inputs) :
  R.v37251 (state s) (inputs i) = Zmod.unsigned (N.v37251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37251 s i)) at 1.
  unfold R.v37251, N.v37251.
  rewrite ?node_37246.
  rewrite ?node_37250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37252 (s : N.State) (i : N.Inputs) :
  R.v37252 (state s) (inputs i) = Zmod.unsigned (N.v37252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37252 s i)) at 1.
  unfold R.v37252, N.v37252.
  unfold R.v6, N.v6.
  rewrite ?node_37251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37253 (s : N.State) (i : N.Inputs) :
  R.v37253 (state s) (inputs i) = Zmod.unsigned (N.v37253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37253 s i)) at 1.
  unfold R.v37253, N.v37253.
  rewrite ?node_15872.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37254 (s : N.State) (i : N.Inputs) :
  R.v37254 (state s) (inputs i) = Zmod.unsigned (N.v37254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37254 s i)) at 1.
  unfold R.v37254, N.v37254.
  unfold R.v6, N.v6.
  rewrite ?node_15915.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37255 (s : N.State) (i : N.Inputs) :
  R.v37255 (state s) (inputs i) = Zmod.unsigned (N.v37255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37255 s i)) at 1.
  unfold R.v37255, N.v37255.
  rewrite ?node_37253.
  rewrite ?node_37254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37256 (s : N.State) (i : N.Inputs) :
  R.v37256 (state s) (inputs i) = Zmod.unsigned (N.v37256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37256 s i)) at 1.
  unfold R.v37256, N.v37256.
  rewrite ?node_37252.
  rewrite ?node_37255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37257 (s : N.State) (i : N.Inputs) :
  R.v37257 (state s) (inputs i) = Zmod.unsigned (N.v37257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37257 s i)) at 1.
  unfold R.v37257, N.v37257.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37258 (s : N.State) (i : N.Inputs) :
  R.v37258 (state s) (inputs i) = Zmod.unsigned (N.v37258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37258 s i)) at 1.
  unfold R.v37258, N.v37258.
  rewrite ?node_15876.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37259 (s : N.State) (i : N.Inputs) :
  R.v37259 (state s) (inputs i) = Zmod.unsigned (N.v37259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37259 s i)) at 1.
  unfold R.v37259, N.v37259.
  unfold R.v6, N.v6.
  rewrite !state_r2229_nr_5F2254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2229_nr_5F2254 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37260 (s : N.State) (i : N.Inputs) :
  R.v37260 (state s) (inputs i) = Zmod.unsigned (N.v37260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37260 s i)) at 1.
  unfold R.v37260, N.v37260.
  unfold R.v6, N.v6.
  rewrite ?node_15872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37261 (s : N.State) (i : N.Inputs) :
  R.v37261 (state s) (inputs i) = Zmod.unsigned (N.v37261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37261 s i)) at 1.
  unfold R.v37261, N.v37261.
  rewrite ?node_37259.
  rewrite ?node_37260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37262 (s : N.State) (i : N.Inputs) :
  R.v37262 (state s) (inputs i) = Zmod.unsigned (N.v37262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37262 s i)) at 1.
  unfold R.v37262, N.v37262.
  unfold R.v16484, N.v16484.
  rewrite ?node_37261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37263 (s : N.State) (i : N.Inputs) :
  R.v37263 (state s) (inputs i) = Zmod.unsigned (N.v37263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37263 s i)) at 1.
  unfold R.v37263, N.v37263.
  rewrite ?node_37258.
  rewrite ?node_37262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37264 (s : N.State) (i : N.Inputs) :
  R.v37264 (state s) (inputs i) = Zmod.unsigned (N.v37264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37264 s i)) at 1.
  unfold R.v37264, N.v37264.
  unfold R.v6, N.v6.
  rewrite ?node_37263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37265 (s : N.State) (i : N.Inputs) :
  R.v37265 (state s) (inputs i) = Zmod.unsigned (N.v37265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37265 s i)) at 1.
  unfold R.v37265, N.v37265.
  rewrite ?node_15877.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37266 (s : N.State) (i : N.Inputs) :
  R.v37266 (state s) (inputs i) = Zmod.unsigned (N.v37266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37266 s i)) at 1.
  unfold R.v37266, N.v37266.
  unfold R.v6, N.v6.
  rewrite ?node_15927.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37267 (s : N.State) (i : N.Inputs) :
  R.v37267 (state s) (inputs i) = Zmod.unsigned (N.v37267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37267 s i)) at 1.
  unfold R.v37267, N.v37267.
  rewrite ?node_37265.
  rewrite ?node_37266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37268 (s : N.State) (i : N.Inputs) :
  R.v37268 (state s) (inputs i) = Zmod.unsigned (N.v37268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37268 s i)) at 1.
  unfold R.v37268, N.v37268.
  rewrite ?node_37264.
  rewrite ?node_37267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37269 (s : N.State) (i : N.Inputs) :
  R.v37269 (state s) (inputs i) = Zmod.unsigned (N.v37269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37269 s i)) at 1.
  unfold R.v37269, N.v37269.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37270 (s : N.State) (i : N.Inputs) :
  R.v37270 (state s) (inputs i) = Zmod.unsigned (N.v37270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37270 s i)) at 1.
  unfold R.v37270, N.v37270.
  rewrite ?node_15908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37271 (s : N.State) (i : N.Inputs) :
  R.v37271 (state s) (inputs i) = Zmod.unsigned (N.v37271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37271 s i)) at 1.
  unfold R.v37271, N.v37271.
  unfold R.v16463, N.v16463.
  rewrite !state_r2233_nr_5F2258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2233_nr_5F2258 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37272 (s : N.State) (i : N.Inputs) :
  R.v37272 (state s) (inputs i) = Zmod.unsigned (N.v37272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37272 s i)) at 1.
  unfold R.v37272, N.v37272.
  unfold R.v16463, N.v16463.
  rewrite !state_r2232_nr_5F2257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2232_nr_5F2257 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37273 (s : N.State) (i : N.Inputs) :
  R.v37273 (state s) (inputs i) = Zmod.unsigned (N.v37273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37273 s i)) at 1.
  unfold R.v37273, N.v37273.
  unfold R.v6, N.v6.
  rewrite !state_r2231_nr_5F2256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2231_nr_5F2256 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37274 (s : N.State) (i : N.Inputs) :
  R.v37274 (state s) (inputs i) = Zmod.unsigned (N.v37274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37274 s i)) at 1.
  unfold R.v37274, N.v37274.
  unfold R.v6, N.v6.
  rewrite !state_r2230_nr_5F2255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2230_nr_5F2255 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37275 (s : N.State) (i : N.Inputs) :
  R.v37275 (state s) (inputs i) = Zmod.unsigned (N.v37275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37275 s i)) at 1.
  unfold R.v37275, N.v37275.
  rewrite ?node_37273.
  rewrite ?node_37274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37276 (s : N.State) (i : N.Inputs) :
  R.v37276 (state s) (inputs i) = Zmod.unsigned (N.v37276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37276 s i)) at 1.
  unfold R.v37276, N.v37276.
  unfold R.v16484, N.v16484.
  rewrite ?node_37275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37277 (s : N.State) (i : N.Inputs) :
  R.v37277 (state s) (inputs i) = Zmod.unsigned (N.v37277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37277 s i)) at 1.
  unfold R.v37277, N.v37277.
  rewrite ?node_37270.
  rewrite ?node_37271.
  rewrite ?node_37272.
  rewrite ?node_37276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37278 (s : N.State) (i : N.Inputs) :
  R.v37278 (state s) (inputs i) = Zmod.unsigned (N.v37278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37278 s i)) at 1.
  unfold R.v37278, N.v37278.
  unfold R.v6, N.v6.
  rewrite ?node_37277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37279 (s : N.State) (i : N.Inputs) :
  R.v37279 (state s) (inputs i) = Zmod.unsigned (N.v37279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37279 s i)) at 1.
  unfold R.v37279, N.v37279.
  rewrite ?node_15909.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37280 (s : N.State) (i : N.Inputs) :
  R.v37280 (state s) (inputs i) = Zmod.unsigned (N.v37280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37280 s i)) at 1.
  unfold R.v37280, N.v37280.
  unfold R.v6, N.v6.
  rewrite ?node_15945.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37281 (s : N.State) (i : N.Inputs) :
  R.v37281 (state s) (inputs i) = Zmod.unsigned (N.v37281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37281 s i)) at 1.
  unfold R.v37281, N.v37281.
  unfold R.v6, N.v6.
  rewrite ?node_15952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37282 (s : N.State) (i : N.Inputs) :
  R.v37282 (state s) (inputs i) = Zmod.unsigned (N.v37282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37282 s i)) at 1.
  unfold R.v37282, N.v37282.
  rewrite ?node_37279.
  rewrite ?node_37280.
  rewrite ?node_37281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37283 (s : N.State) (i : N.Inputs) :
  R.v37283 (state s) (inputs i) = Zmod.unsigned (N.v37283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37283 s i)) at 1.
  unfold R.v37283, N.v37283.
  rewrite ?node_37278.
  rewrite ?node_37282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37284 (s : N.State) (i : N.Inputs) :
  R.v37284 (state s) (inputs i) = Zmod.unsigned (N.v37284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37284 s i)) at 1.
  unfold R.v37284, N.v37284.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37285 (s : N.State) (i : N.Inputs) :
  R.v37285 (state s) (inputs i) = Zmod.unsigned (N.v37285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37285 s i)) at 1.
  unfold R.v37285, N.v37285.
  unfold R.v16463, N.v16463.
  rewrite !state_r2232_nr_5F2257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2232_nr_5F2257 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37286 (s : N.State) (i : N.Inputs) :
  R.v37286 (state s) (inputs i) = Zmod.unsigned (N.v37286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37286 s i)) at 1.
  unfold R.v37286, N.v37286.
  unfold R.v6, N.v6.
  rewrite !state_r2231_nr_5F2256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2231_nr_5F2256 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37287 (s : N.State) (i : N.Inputs) :
  R.v37287 (state s) (inputs i) = Zmod.unsigned (N.v37287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37287 s i)) at 1.
  unfold R.v37287, N.v37287.
  unfold R.v6, N.v6.
  rewrite !state_r2230_nr_5F2255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2230_nr_5F2255 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37288 (s : N.State) (i : N.Inputs) :
  R.v37288 (state s) (inputs i) = Zmod.unsigned (N.v37288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37288 s i)) at 1.
  unfold R.v37288, N.v37288.
  rewrite ?node_37286.
  rewrite ?node_37287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37289 (s : N.State) (i : N.Inputs) :
  R.v37289 (state s) (inputs i) = Zmod.unsigned (N.v37289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37289 s i)) at 1.
  unfold R.v37289, N.v37289.
  unfold R.v16484, N.v16484.
  rewrite ?node_37288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37290 (s : N.State) (i : N.Inputs) :
  R.v37290 (state s) (inputs i) = Zmod.unsigned (N.v37290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37290 s i)) at 1.
  unfold R.v37290, N.v37290.
  rewrite ?node_37285.
  rewrite ?node_37289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37291 (s : N.State) (i : N.Inputs) :
  R.v37291 (state s) (inputs i) = Zmod.unsigned (N.v37291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37291 s i)) at 1.
  unfold R.v37291, N.v37291.
  unfold R.v6, N.v6.
  rewrite ?node_37290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37292 (s : N.State) (i : N.Inputs) :
  R.v37292 (state s) (inputs i) = Zmod.unsigned (N.v37292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37292 s i)) at 1.
  unfold R.v37292, N.v37292.
  rewrite ?node_15905.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37293 (s : N.State) (i : N.Inputs) :
  R.v37293 (state s) (inputs i) = Zmod.unsigned (N.v37293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37293 s i)) at 1.
  unfold R.v37293, N.v37293.
  unfold R.v6, N.v6.
  rewrite ?node_15945.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37294 (s : N.State) (i : N.Inputs) :
  R.v37294 (state s) (inputs i) = Zmod.unsigned (N.v37294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37294 s i)) at 1.
  unfold R.v37294, N.v37294.
  rewrite ?node_37292.
  rewrite ?node_37293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37295 (s : N.State) (i : N.Inputs) :
  R.v37295 (state s) (inputs i) = Zmod.unsigned (N.v37295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37295 s i)) at 1.
  unfold R.v37295, N.v37295.
  rewrite ?node_37291.
  rewrite ?node_37294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37296 (s : N.State) (i : N.Inputs) :
  R.v37296 (state s) (inputs i) = Zmod.unsigned (N.v37296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37296 s i)) at 1.
  unfold R.v37296, N.v37296.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37297 (s : N.State) (i : N.Inputs) :
  R.v37297 (state s) (inputs i) = Zmod.unsigned (N.v37297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37297 s i)) at 1.
  unfold R.v37297, N.v37297.
  rewrite ?node_15908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37298 (s : N.State) (i : N.Inputs) :
  R.v37298 (state s) (inputs i) = Zmod.unsigned (N.v37298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37298 s i)) at 1.
  unfold R.v37298, N.v37298.
  unfold R.v6, N.v6.
  rewrite !state_r2233_nr_5F2258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2233_nr_5F2258 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37299 (s : N.State) (i : N.Inputs) :
  R.v37299 (state s) (inputs i) = Zmod.unsigned (N.v37299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37299 s i)) at 1.
  unfold R.v37299, N.v37299.
  unfold R.v6, N.v6.
  rewrite ?node_15905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37300 (s : N.State) (i : N.Inputs) :
  R.v37300 (state s) (inputs i) = Zmod.unsigned (N.v37300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37300 s i)) at 1.
  unfold R.v37300, N.v37300.
  rewrite ?node_37298.
  rewrite ?node_37299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37301 (s : N.State) (i : N.Inputs) :
  R.v37301 (state s) (inputs i) = Zmod.unsigned (N.v37301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37301 s i)) at 1.
  unfold R.v37301, N.v37301.
  unfold R.v16484, N.v16484.
  rewrite ?node_37300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37302 (s : N.State) (i : N.Inputs) :
  R.v37302 (state s) (inputs i) = Zmod.unsigned (N.v37302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37302 s i)) at 1.
  unfold R.v37302, N.v37302.
  rewrite ?node_37297.
  rewrite ?node_37301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37303 (s : N.State) (i : N.Inputs) :
  R.v37303 (state s) (inputs i) = Zmod.unsigned (N.v37303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37303 s i)) at 1.
  unfold R.v37303, N.v37303.
  unfold R.v6, N.v6.
  rewrite ?node_37302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37304 (s : N.State) (i : N.Inputs) :
  R.v37304 (state s) (inputs i) = Zmod.unsigned (N.v37304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37304 s i)) at 1.
  unfold R.v37304, N.v37304.
  rewrite ?node_15909.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37305 (s : N.State) (i : N.Inputs) :
  R.v37305 (state s) (inputs i) = Zmod.unsigned (N.v37305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37305 s i)) at 1.
  unfold R.v37305, N.v37305.
  unfold R.v6, N.v6.
  rewrite ?node_15952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37306 (s : N.State) (i : N.Inputs) :
  R.v37306 (state s) (inputs i) = Zmod.unsigned (N.v37306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37306 s i)) at 1.
  unfold R.v37306, N.v37306.
  rewrite ?node_37304.
  rewrite ?node_37305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37307 (s : N.State) (i : N.Inputs) :
  R.v37307 (state s) (inputs i) = Zmod.unsigned (N.v37307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37307 s i)) at 1.
  unfold R.v37307, N.v37307.
  rewrite ?node_37303.
  rewrite ?node_37306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37308 (s : N.State) (i : N.Inputs) :
  R.v37308 (state s) (inputs i) = Zmod.unsigned (N.v37308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37308 s i)) at 1.
  unfold R.v37308, N.v37308.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37309 (s : N.State) (i : N.Inputs) :
  R.v37309 (state s) (inputs i) = Zmod.unsigned (N.v37309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37309 s i)) at 1.
  unfold R.v37309, N.v37309.
  unfold R.v16463, N.v16463.
  rewrite !state_r2236_nr_5F2261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2236_nr_5F2261 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37310 (s : N.State) (i : N.Inputs) :
  R.v37310 (state s) (inputs i) = Zmod.unsigned (N.v37310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37310 s i)) at 1.
  unfold R.v37310, N.v37310.
  unfold R.v6, N.v6.
  rewrite !state_r2235_nr_5F2260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2235_nr_5F2260 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37311 (s : N.State) (i : N.Inputs) :
  R.v37311 (state s) (inputs i) = Zmod.unsigned (N.v37311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37311 s i)) at 1.
  unfold R.v37311, N.v37311.
  unfold R.v6, N.v6.
  rewrite !state_r2234_nr_5F2259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2234_nr_5F2259 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37312 (s : N.State) (i : N.Inputs) :
  R.v37312 (state s) (inputs i) = Zmod.unsigned (N.v37312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37312 s i)) at 1.
  unfold R.v37312, N.v37312.
  rewrite ?node_37310.
  rewrite ?node_37311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37313 (s : N.State) (i : N.Inputs) :
  R.v37313 (state s) (inputs i) = Zmod.unsigned (N.v37313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37313 s i)) at 1.
  unfold R.v37313, N.v37313.
  unfold R.v16484, N.v16484.
  rewrite ?node_37312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37314 (s : N.State) (i : N.Inputs) :
  R.v37314 (state s) (inputs i) = Zmod.unsigned (N.v37314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37314 s i)) at 1.
  unfold R.v37314, N.v37314.
  rewrite ?node_37309.
  rewrite ?node_37313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37315 (s : N.State) (i : N.Inputs) :
  R.v37315 (state s) (inputs i) = Zmod.unsigned (N.v37315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37315 s i)) at 1.
  unfold R.v37315, N.v37315.
  unfold R.v6, N.v6.
  rewrite ?node_37314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37316 (s : N.State) (i : N.Inputs) :
  R.v37316 (state s) (inputs i) = Zmod.unsigned (N.v37316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37316 s i)) at 1.
  unfold R.v37316, N.v37316.
  rewrite ?node_15911.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37317 (s : N.State) (i : N.Inputs) :
  R.v37317 (state s) (inputs i) = Zmod.unsigned (N.v37317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37317 s i)) at 1.
  unfold R.v37317, N.v37317.
  unfold R.v6, N.v6.
  rewrite ?node_15956.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37318 (s : N.State) (i : N.Inputs) :
  R.v37318 (state s) (inputs i) = Zmod.unsigned (N.v37318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37318 s i)) at 1.
  unfold R.v37318, N.v37318.
  rewrite ?node_37316.
  rewrite ?node_37317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37319 (s : N.State) (i : N.Inputs) :
  R.v37319 (state s) (inputs i) = Zmod.unsigned (N.v37319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37319 s i)) at 1.
  unfold R.v37319, N.v37319.
  rewrite ?node_37315.
  rewrite ?node_37318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37320 (s : N.State) (i : N.Inputs) :
  R.v37320 (state s) (inputs i) = Zmod.unsigned (N.v37320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37320 s i)) at 1.
  unfold R.v37320, N.v37320.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37321 (s : N.State) (i : N.Inputs) :
  R.v37321 (state s) (inputs i) = Zmod.unsigned (N.v37321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37321 s i)) at 1.
  unfold R.v37321, N.v37321.
  rewrite ?node_15945.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37322 (s : N.State) (i : N.Inputs) :
  R.v37322 (state s) (inputs i) = Zmod.unsigned (N.v37322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37322 s i)) at 1.
  unfold R.v37322, N.v37322.
  unfold R.v16463, N.v16463.
  rewrite !state_r2239_nr_5F2265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2239_nr_5F2265 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37323 (s : N.State) (i : N.Inputs) :
  R.v37323 (state s) (inputs i) = Zmod.unsigned (N.v37323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37323 s i)) at 1.
  unfold R.v37323, N.v37323.
  unfold R.v16463, N.v16463.
  rewrite !state_r2238_nr_5F2264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2238_nr_5F2264 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37324 (s : N.State) (i : N.Inputs) :
  R.v37324 (state s) (inputs i) = Zmod.unsigned (N.v37324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37324 s i)) at 1.
  unfold R.v37324, N.v37324.
  unfold R.v6, N.v6.
  rewrite !state_r2237_nr_5F2263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2237_nr_5F2263 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37325 (s : N.State) (i : N.Inputs) :
  R.v37325 (state s) (inputs i) = Zmod.unsigned (N.v37325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37325 s i)) at 1.
  unfold R.v37325, N.v37325.
  unfold R.v19, N.v19.
  rewrite ?node_37324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37326 (s : N.State) (i : N.Inputs) :
  R.v37326 (state s) (inputs i) = Zmod.unsigned (N.v37326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37326 s i)) at 1.
  unfold R.v37326, N.v37326.
  unfold R.v16484, N.v16484.
  rewrite ?node_37325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37327 (s : N.State) (i : N.Inputs) :
  R.v37327 (state s) (inputs i) = Zmod.unsigned (N.v37327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37327 s i)) at 1.
  unfold R.v37327, N.v37327.
  rewrite ?node_37321.
  rewrite ?node_37322.
  rewrite ?node_37323.
  rewrite ?node_37326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37328 (s : N.State) (i : N.Inputs) :
  R.v37328 (state s) (inputs i) = Zmod.unsigned (N.v37328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37328 s i)) at 1.
  unfold R.v37328, N.v37328.
  unfold R.v6, N.v6.
  rewrite ?node_37327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37329 (s : N.State) (i : N.Inputs) :
  R.v37329 (state s) (inputs i) = Zmod.unsigned (N.v37329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37329 s i)) at 1.
  unfold R.v37329, N.v37329.
  rewrite ?node_15946.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37330 (s : N.State) (i : N.Inputs) :
  R.v37330 (state s) (inputs i) = Zmod.unsigned (N.v37330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37330 s i)) at 1.
  unfold R.v37330, N.v37330.
  unfold R.v6, N.v6.
  rewrite ?node_15979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37331 (s : N.State) (i : N.Inputs) :
  R.v37331 (state s) (inputs i) = Zmod.unsigned (N.v37331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37331 s i)) at 1.
  unfold R.v37331, N.v37331.
  unfold R.v6, N.v6.
  rewrite ?node_15985.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37332 (s : N.State) (i : N.Inputs) :
  R.v37332 (state s) (inputs i) = Zmod.unsigned (N.v37332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37332 s i)) at 1.
  unfold R.v37332, N.v37332.
  rewrite ?node_37329.
  rewrite ?node_37330.
  rewrite ?node_37331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37333 (s : N.State) (i : N.Inputs) :
  R.v37333 (state s) (inputs i) = Zmod.unsigned (N.v37333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37333 s i)) at 1.
  unfold R.v37333, N.v37333.
  rewrite ?node_37328.
  rewrite ?node_37332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37334 (s : N.State) (i : N.Inputs) :
  R.v37334 (state s) (inputs i) = Zmod.unsigned (N.v37334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37334 s i)) at 1.
  unfold R.v37334, N.v37334.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37335 (s : N.State) (i : N.Inputs) :
  R.v37335 (state s) (inputs i) = Zmod.unsigned (N.v37335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37335 s i)) at 1.
  unfold R.v37335, N.v37335.
  unfold R.v16463, N.v16463.
  rewrite !state_r2238_nr_5F2264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2238_nr_5F2264 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37336 (s : N.State) (i : N.Inputs) :
  R.v37336 (state s) (inputs i) = Zmod.unsigned (N.v37336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37336 s i)) at 1.
  unfold R.v37336, N.v37336.
  unfold R.v6, N.v6.
  rewrite !state_r2237_nr_5F2263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2237_nr_5F2263 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37337 (s : N.State) (i : N.Inputs) :
  R.v37337 (state s) (inputs i) = Zmod.unsigned (N.v37337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37337 s i)) at 1.
  unfold R.v37337, N.v37337.
  unfold R.v19, N.v19.
  rewrite ?node_37336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37338 (s : N.State) (i : N.Inputs) :
  R.v37338 (state s) (inputs i) = Zmod.unsigned (N.v37338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37338 s i)) at 1.
  unfold R.v37338, N.v37338.
  unfold R.v16484, N.v16484.
  rewrite ?node_37337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37339 (s : N.State) (i : N.Inputs) :
  R.v37339 (state s) (inputs i) = Zmod.unsigned (N.v37339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37339 s i)) at 1.
  unfold R.v37339, N.v37339.
  rewrite ?node_37335.
  rewrite ?node_37338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37340 (s : N.State) (i : N.Inputs) :
  R.v37340 (state s) (inputs i) = Zmod.unsigned (N.v37340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37340 s i)) at 1.
  unfold R.v37340, N.v37340.
  unfold R.v6, N.v6.
  rewrite ?node_37339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37341 (s : N.State) (i : N.Inputs) :
  R.v37341 (state s) (inputs i) = Zmod.unsigned (N.v37341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37341 s i)) at 1.
  unfold R.v37341, N.v37341.
  rewrite ?node_15941.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37342 (s : N.State) (i : N.Inputs) :
  R.v37342 (state s) (inputs i) = Zmod.unsigned (N.v37342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37342 s i)) at 1.
  unfold R.v37342, N.v37342.
  unfold R.v6, N.v6.
  rewrite ?node_15979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37343 (s : N.State) (i : N.Inputs) :
  R.v37343 (state s) (inputs i) = Zmod.unsigned (N.v37343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37343 s i)) at 1.
  unfold R.v37343, N.v37343.
  rewrite ?node_37341.
  rewrite ?node_37342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37344 (s : N.State) (i : N.Inputs) :
  R.v37344 (state s) (inputs i) = Zmod.unsigned (N.v37344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37344 s i)) at 1.
  unfold R.v37344, N.v37344.
  rewrite ?node_37340.
  rewrite ?node_37343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37345 (s : N.State) (i : N.Inputs) :
  R.v37345 (state s) (inputs i) = Zmod.unsigned (N.v37345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37345 s i)) at 1.
  unfold R.v37345, N.v37345.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37346 (s : N.State) (i : N.Inputs) :
  R.v37346 (state s) (inputs i) = Zmod.unsigned (N.v37346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37346 s i)) at 1.
  unfold R.v37346, N.v37346.
  rewrite ?node_15945.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37347 (s : N.State) (i : N.Inputs) :
  R.v37347 (state s) (inputs i) = Zmod.unsigned (N.v37347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37347 s i)) at 1.
  unfold R.v37347, N.v37347.
  unfold R.v6, N.v6.
  rewrite !state_r2239_nr_5F2265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2239_nr_5F2265 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37348 (s : N.State) (i : N.Inputs) :
  R.v37348 (state s) (inputs i) = Zmod.unsigned (N.v37348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37348 s i)) at 1.
  unfold R.v37348, N.v37348.
  unfold R.v6, N.v6.
  rewrite ?node_15941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37349 (s : N.State) (i : N.Inputs) :
  R.v37349 (state s) (inputs i) = Zmod.unsigned (N.v37349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37349 s i)) at 1.
  unfold R.v37349, N.v37349.
  rewrite ?node_37347.
  rewrite ?node_37348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37350 (s : N.State) (i : N.Inputs) :
  R.v37350 (state s) (inputs i) = Zmod.unsigned (N.v37350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37350 s i)) at 1.
  unfold R.v37350, N.v37350.
  unfold R.v16484, N.v16484.
  rewrite ?node_37349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37351 (s : N.State) (i : N.Inputs) :
  R.v37351 (state s) (inputs i) = Zmod.unsigned (N.v37351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37351 s i)) at 1.
  unfold R.v37351, N.v37351.
  rewrite ?node_37346.
  rewrite ?node_37350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37352 (s : N.State) (i : N.Inputs) :
  R.v37352 (state s) (inputs i) = Zmod.unsigned (N.v37352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37352 s i)) at 1.
  unfold R.v37352, N.v37352.
  unfold R.v6, N.v6.
  rewrite ?node_37351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37353 (s : N.State) (i : N.Inputs) :
  R.v37353 (state s) (inputs i) = Zmod.unsigned (N.v37353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37353 s i)) at 1.
  unfold R.v37353, N.v37353.
  rewrite ?node_15946.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37354 (s : N.State) (i : N.Inputs) :
  R.v37354 (state s) (inputs i) = Zmod.unsigned (N.v37354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37354 s i)) at 1.
  unfold R.v37354, N.v37354.
  unfold R.v6, N.v6.
  rewrite ?node_15985.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37355 (s : N.State) (i : N.Inputs) :
  R.v37355 (state s) (inputs i) = Zmod.unsigned (N.v37355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37355 s i)) at 1.
  unfold R.v37355, N.v37355.
  rewrite ?node_37353.
  rewrite ?node_37354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37356 (s : N.State) (i : N.Inputs) :
  R.v37356 (state s) (inputs i) = Zmod.unsigned (N.v37356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37356 s i)) at 1.
  unfold R.v37356, N.v37356.
  rewrite ?node_37352.
  rewrite ?node_37355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37357 (s : N.State) (i : N.Inputs) :
  R.v37357 (state s) (inputs i) = Zmod.unsigned (N.v37357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37357 s i)) at 1.
  unfold R.v37357, N.v37357.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37358 (s : N.State) (i : N.Inputs) :
  R.v37358 (state s) (inputs i) = Zmod.unsigned (N.v37358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37358 s i)) at 1.
  unfold R.v37358, N.v37358.
  unfold R.v16463, N.v16463.
  rewrite !state_r2242_nr_5F2268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2242_nr_5F2268 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37359 (s : N.State) (i : N.Inputs) :
  R.v37359 (state s) (inputs i) = Zmod.unsigned (N.v37359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37359 s i)) at 1.
  unfold R.v37359, N.v37359.
  unfold R.v6, N.v6.
  rewrite !state_r2241_nr_5F2267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2241_nr_5F2267 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37360 (s : N.State) (i : N.Inputs) :
  R.v37360 (state s) (inputs i) = Zmod.unsigned (N.v37360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37360 s i)) at 1.
  unfold R.v37360, N.v37360.
  unfold R.v6, N.v6.
  rewrite !state_r2240_nr_5F2266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2240_nr_5F2266 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37361 (s : N.State) (i : N.Inputs) :
  R.v37361 (state s) (inputs i) = Zmod.unsigned (N.v37361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37361 s i)) at 1.
  unfold R.v37361, N.v37361.
  rewrite ?node_37359.
  rewrite ?node_37360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37362 (s : N.State) (i : N.Inputs) :
  R.v37362 (state s) (inputs i) = Zmod.unsigned (N.v37362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37362 s i)) at 1.
  unfold R.v37362, N.v37362.
  unfold R.v16484, N.v16484.
  rewrite ?node_37361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37363 (s : N.State) (i : N.Inputs) :
  R.v37363 (state s) (inputs i) = Zmod.unsigned (N.v37363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37363 s i)) at 1.
  unfold R.v37363, N.v37363.
  rewrite ?node_37358.
  rewrite ?node_37362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37364 (s : N.State) (i : N.Inputs) :
  R.v37364 (state s) (inputs i) = Zmod.unsigned (N.v37364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37364 s i)) at 1.
  unfold R.v37364, N.v37364.
  unfold R.v6, N.v6.
  rewrite ?node_37363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37365 (s : N.State) (i : N.Inputs) :
  R.v37365 (state s) (inputs i) = Zmod.unsigned (N.v37365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37365 s i)) at 1.
  unfold R.v37365, N.v37365.
  rewrite ?node_15948.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37366 (s : N.State) (i : N.Inputs) :
  R.v37366 (state s) (inputs i) = Zmod.unsigned (N.v37366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37366 s i)) at 1.
  unfold R.v37366, N.v37366.
  unfold R.v6, N.v6.
  rewrite ?node_15989.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37367 (s : N.State) (i : N.Inputs) :
  R.v37367 (state s) (inputs i) = Zmod.unsigned (N.v37367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37367 s i)) at 1.
  unfold R.v37367, N.v37367.
  rewrite ?node_37365.
  rewrite ?node_37366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37368 (s : N.State) (i : N.Inputs) :
  R.v37368 (state s) (inputs i) = Zmod.unsigned (N.v37368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37368 s i)) at 1.
  unfold R.v37368, N.v37368.
  rewrite ?node_37364.
  rewrite ?node_37367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37369 (s : N.State) (i : N.Inputs) :
  R.v37369 (state s) (inputs i) = Zmod.unsigned (N.v37369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37369 s i)) at 1.
  unfold R.v37369, N.v37369.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37370 (s : N.State) (i : N.Inputs) :
  R.v37370 (state s) (inputs i) = Zmod.unsigned (N.v37370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37370 s i)) at 1.
  unfold R.v37370, N.v37370.
  rewrite ?node_15979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37371 (s : N.State) (i : N.Inputs) :
  R.v37371 (state s) (inputs i) = Zmod.unsigned (N.v37371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37371 s i)) at 1.
  unfold R.v37371, N.v37371.
  unfold R.v16463, N.v16463.
  rewrite !state_r2246_nr_5F2272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2246_nr_5F2272 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37372 (s : N.State) (i : N.Inputs) :
  R.v37372 (state s) (inputs i) = Zmod.unsigned (N.v37372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37372 s i)) at 1.
  unfold R.v37372, N.v37372.
  unfold R.v16463, N.v16463.
  rewrite !state_r2245_nr_5F2271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2245_nr_5F2271 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37373 (s : N.State) (i : N.Inputs) :
  R.v37373 (state s) (inputs i) = Zmod.unsigned (N.v37373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37373 s i)) at 1.
  unfold R.v37373, N.v37373.
  unfold R.v6, N.v6.
  rewrite !state_r2244_nr_5F2270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2244_nr_5F2270 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37374 (s : N.State) (i : N.Inputs) :
  R.v37374 (state s) (inputs i) = Zmod.unsigned (N.v37374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37374 s i)) at 1.
  unfold R.v37374, N.v37374.
  unfold R.v6, N.v6.
  rewrite !state_r2243_nr_5F2269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2243_nr_5F2269 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37375 (s : N.State) (i : N.Inputs) :
  R.v37375 (state s) (inputs i) = Zmod.unsigned (N.v37375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37375 s i)) at 1.
  unfold R.v37375, N.v37375.
  rewrite ?node_37373.
  rewrite ?node_37374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37376 (s : N.State) (i : N.Inputs) :
  R.v37376 (state s) (inputs i) = Zmod.unsigned (N.v37376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37376 s i)) at 1.
  unfold R.v37376, N.v37376.
  unfold R.v16484, N.v16484.
  rewrite ?node_37375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37377 (s : N.State) (i : N.Inputs) :
  R.v37377 (state s) (inputs i) = Zmod.unsigned (N.v37377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37377 s i)) at 1.
  unfold R.v37377, N.v37377.
  rewrite ?node_37370.
  rewrite ?node_37371.
  rewrite ?node_37372.
  rewrite ?node_37376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37378 (s : N.State) (i : N.Inputs) :
  R.v37378 (state s) (inputs i) = Zmod.unsigned (N.v37378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37378 s i)) at 1.
  unfold R.v37378, N.v37378.
  unfold R.v6, N.v6.
  rewrite ?node_37377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37379 (s : N.State) (i : N.Inputs) :
  R.v37379 (state s) (inputs i) = Zmod.unsigned (N.v37379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37379 s i)) at 1.
  unfold R.v37379, N.v37379.
  rewrite ?node_15980.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37380 (s : N.State) (i : N.Inputs) :
  R.v37380 (state s) (inputs i) = Zmod.unsigned (N.v37380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37380 s i)) at 1.
  unfold R.v37380, N.v37380.
  unfold R.v6, N.v6.
  rewrite ?node_16011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37381 (s : N.State) (i : N.Inputs) :
  R.v37381 (state s) (inputs i) = Zmod.unsigned (N.v37381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37381 s i)) at 1.
  unfold R.v37381, N.v37381.
  unfold R.v6, N.v6.
  rewrite ?node_16017.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37382 (s : N.State) (i : N.Inputs) :
  R.v37382 (state s) (inputs i) = Zmod.unsigned (N.v37382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37382 s i)) at 1.
  unfold R.v37382, N.v37382.
  rewrite ?node_37379.
  rewrite ?node_37380.
  rewrite ?node_37381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37383 (s : N.State) (i : N.Inputs) :
  R.v37383 (state s) (inputs i) = Zmod.unsigned (N.v37383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37383 s i)) at 1.
  unfold R.v37383, N.v37383.
  rewrite ?node_37378.
  rewrite ?node_37382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37384 (s : N.State) (i : N.Inputs) :
  R.v37384 (state s) (inputs i) = Zmod.unsigned (N.v37384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37384 s i)) at 1.
  unfold R.v37384, N.v37384.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37385 (s : N.State) (i : N.Inputs) :
  R.v37385 (state s) (inputs i) = Zmod.unsigned (N.v37385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37385 s i)) at 1.
  unfold R.v37385, N.v37385.
  unfold R.v16463, N.v16463.
  rewrite !state_r2245_nr_5F2271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2245_nr_5F2271 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37386 (s : N.State) (i : N.Inputs) :
  R.v37386 (state s) (inputs i) = Zmod.unsigned (N.v37386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37386 s i)) at 1.
  unfold R.v37386, N.v37386.
  unfold R.v6, N.v6.
  rewrite !state_r2244_nr_5F2270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2244_nr_5F2270 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37387 (s : N.State) (i : N.Inputs) :
  R.v37387 (state s) (inputs i) = Zmod.unsigned (N.v37387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37387 s i)) at 1.
  unfold R.v37387, N.v37387.
  unfold R.v6, N.v6.
  rewrite !state_r2243_nr_5F2269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2243_nr_5F2269 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37388 (s : N.State) (i : N.Inputs) :
  R.v37388 (state s) (inputs i) = Zmod.unsigned (N.v37388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37388 s i)) at 1.
  unfold R.v37388, N.v37388.
  rewrite ?node_37386.
  rewrite ?node_37387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37389 (s : N.State) (i : N.Inputs) :
  R.v37389 (state s) (inputs i) = Zmod.unsigned (N.v37389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37389 s i)) at 1.
  unfold R.v37389, N.v37389.
  unfold R.v16484, N.v16484.
  rewrite ?node_37388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37390 (s : N.State) (i : N.Inputs) :
  R.v37390 (state s) (inputs i) = Zmod.unsigned (N.v37390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37390 s i)) at 1.
  unfold R.v37390, N.v37390.
  rewrite ?node_37385.
  rewrite ?node_37389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37391 (s : N.State) (i : N.Inputs) :
  R.v37391 (state s) (inputs i) = Zmod.unsigned (N.v37391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37391 s i)) at 1.
  unfold R.v37391, N.v37391.
  unfold R.v6, N.v6.
  rewrite ?node_37390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37392 (s : N.State) (i : N.Inputs) :
  R.v37392 (state s) (inputs i) = Zmod.unsigned (N.v37392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37392 s i)) at 1.
  unfold R.v37392, N.v37392.
  rewrite ?node_15976.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37393 (s : N.State) (i : N.Inputs) :
  R.v37393 (state s) (inputs i) = Zmod.unsigned (N.v37393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37393 s i)) at 1.
  unfold R.v37393, N.v37393.
  unfold R.v6, N.v6.
  rewrite ?node_16011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37394 (s : N.State) (i : N.Inputs) :
  R.v37394 (state s) (inputs i) = Zmod.unsigned (N.v37394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37394 s i)) at 1.
  unfold R.v37394, N.v37394.
  rewrite ?node_37392.
  rewrite ?node_37393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37395 (s : N.State) (i : N.Inputs) :
  R.v37395 (state s) (inputs i) = Zmod.unsigned (N.v37395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37395 s i)) at 1.
  unfold R.v37395, N.v37395.
  rewrite ?node_37391.
  rewrite ?node_37394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37396 (s : N.State) (i : N.Inputs) :
  R.v37396 (state s) (inputs i) = Zmod.unsigned (N.v37396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37396 s i)) at 1.
  unfold R.v37396, N.v37396.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37397 (s : N.State) (i : N.Inputs) :
  R.v37397 (state s) (inputs i) = Zmod.unsigned (N.v37397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37397 s i)) at 1.
  unfold R.v37397, N.v37397.
  rewrite ?node_15979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37398 (s : N.State) (i : N.Inputs) :
  R.v37398 (state s) (inputs i) = Zmod.unsigned (N.v37398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37398 s i)) at 1.
  unfold R.v37398, N.v37398.
  unfold R.v6, N.v6.
  rewrite !state_r2246_nr_5F2272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2246_nr_5F2272 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37399 (s : N.State) (i : N.Inputs) :
  R.v37399 (state s) (inputs i) = Zmod.unsigned (N.v37399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37399 s i)) at 1.
  unfold R.v37399, N.v37399.
  unfold R.v6, N.v6.
  rewrite ?node_15976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37400 (s : N.State) (i : N.Inputs) :
  R.v37400 (state s) (inputs i) = Zmod.unsigned (N.v37400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37400 s i)) at 1.
  unfold R.v37400, N.v37400.
  rewrite ?node_37398.
  rewrite ?node_37399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37401 (s : N.State) (i : N.Inputs) :
  R.v37401 (state s) (inputs i) = Zmod.unsigned (N.v37401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37401 s i)) at 1.
  unfold R.v37401, N.v37401.
  unfold R.v16484, N.v16484.
  rewrite ?node_37400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37402 (s : N.State) (i : N.Inputs) :
  R.v37402 (state s) (inputs i) = Zmod.unsigned (N.v37402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37402 s i)) at 1.
  unfold R.v37402, N.v37402.
  rewrite ?node_37397.
  rewrite ?node_37401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37403 (s : N.State) (i : N.Inputs) :
  R.v37403 (state s) (inputs i) = Zmod.unsigned (N.v37403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37403 s i)) at 1.
  unfold R.v37403, N.v37403.
  unfold R.v6, N.v6.
  rewrite ?node_37402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37404 (s : N.State) (i : N.Inputs) :
  R.v37404 (state s) (inputs i) = Zmod.unsigned (N.v37404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37404 s i)) at 1.
  unfold R.v37404, N.v37404.
  rewrite ?node_15980.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37405 (s : N.State) (i : N.Inputs) :
  R.v37405 (state s) (inputs i) = Zmod.unsigned (N.v37405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37405 s i)) at 1.
  unfold R.v37405, N.v37405.
  unfold R.v6, N.v6.
  rewrite ?node_16017.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37406 (s : N.State) (i : N.Inputs) :
  R.v37406 (state s) (inputs i) = Zmod.unsigned (N.v37406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37406 s i)) at 1.
  unfold R.v37406, N.v37406.
  rewrite ?node_37404.
  rewrite ?node_37405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37407 (s : N.State) (i : N.Inputs) :
  R.v37407 (state s) (inputs i) = Zmod.unsigned (N.v37407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37407 s i)) at 1.
  unfold R.v37407, N.v37407.
  rewrite ?node_37403.
  rewrite ?node_37406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37408 (s : N.State) (i : N.Inputs) :
  R.v37408 (state s) (inputs i) = Zmod.unsigned (N.v37408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37408 s i)) at 1.
  unfold R.v37408, N.v37408.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37409 (s : N.State) (i : N.Inputs) :
  R.v37409 (state s) (inputs i) = Zmod.unsigned (N.v37409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37409 s i)) at 1.
  unfold R.v37409, N.v37409.
  unfold R.v6, N.v6.
  rewrite !state_r2248_nr_5F2274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2248_nr_5F2274 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37410 (s : N.State) (i : N.Inputs) :
  R.v37410 (state s) (inputs i) = Zmod.unsigned (N.v37410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37410 s i)) at 1.
  unfold R.v37410, N.v37410.
  unfold R.v6, N.v6.
  rewrite !state_r2247_nr_5F2273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2247_nr_5F2273 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37411 (s : N.State) (i : N.Inputs) :
  R.v37411 (state s) (inputs i) = Zmod.unsigned (N.v37411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37411 s i)) at 1.
  unfold R.v37411, N.v37411.
  rewrite ?node_37409.
  rewrite ?node_37410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37412 (s : N.State) (i : N.Inputs) :
  R.v37412 (state s) (inputs i) = Zmod.unsigned (N.v37412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37412 s i)) at 1.
  unfold R.v37412, N.v37412.
  unfold R.v16463, N.v16463.
  rewrite ?node_37411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37413 (s : N.State) (i : N.Inputs) :
  R.v37413 (state s) (inputs i) = Zmod.unsigned (N.v37413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37413 s i)) at 1.
  unfold R.v37413, N.v37413.
  rewrite ?node_15981.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37414 (s : N.State) (i : N.Inputs) :
  R.v37414 (state s) (inputs i) = Zmod.unsigned (N.v37414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37414 s i)) at 1.
  unfold R.v37414, N.v37414.
  unfold R.v6, N.v6.
  rewrite ?node_16019.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37415 (s : N.State) (i : N.Inputs) :
  R.v37415 (state s) (inputs i) = Zmod.unsigned (N.v37415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37415 s i)) at 1.
  unfold R.v37415, N.v37415.
  rewrite ?node_37413.
  rewrite ?node_37414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37416 (s : N.State) (i : N.Inputs) :
  R.v37416 (state s) (inputs i) = Zmod.unsigned (N.v37416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37416 s i)) at 1.
  unfold R.v37416, N.v37416.
  rewrite ?node_37412.
  rewrite ?node_37415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37417 (s : N.State) (i : N.Inputs) :
  R.v37417 (state s) (inputs i) = Zmod.unsigned (N.v37417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37417 s i)) at 1.
  unfold R.v37417, N.v37417.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37418 (s : N.State) (i : N.Inputs) :
  R.v37418 (state s) (inputs i) = Zmod.unsigned (N.v37418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37418 s i)) at 1.
  unfold R.v37418, N.v37418.
  rewrite ?node_16011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37419 (s : N.State) (i : N.Inputs) :
  R.v37419 (state s) (inputs i) = Zmod.unsigned (N.v37419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37419 s i)) at 1.
  unfold R.v37419, N.v37419.
  unfold R.v16463, N.v16463.
  rewrite !state_r2251_nr_5F2278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2251_nr_5F2278 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37420 (s : N.State) (i : N.Inputs) :
  R.v37420 (state s) (inputs i) = Zmod.unsigned (N.v37420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37420 s i)) at 1.
  unfold R.v37420, N.v37420.
  unfold R.v16463, N.v16463.
  rewrite !state_r2250_nr_5F2277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2250_nr_5F2277 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37421 (s : N.State) (i : N.Inputs) :
  R.v37421 (state s) (inputs i) = Zmod.unsigned (N.v37421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37421 s i)) at 1.
  unfold R.v37421, N.v37421.
  unfold R.v6, N.v6.
  rewrite !state_r2249_nr_5F2276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2249_nr_5F2276 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37422 (s : N.State) (i : N.Inputs) :
  R.v37422 (state s) (inputs i) = Zmod.unsigned (N.v37422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37422 s i)) at 1.
  unfold R.v37422, N.v37422.
  unfold R.v19, N.v19.
  rewrite ?node_37421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37423 (s : N.State) (i : N.Inputs) :
  R.v37423 (state s) (inputs i) = Zmod.unsigned (N.v37423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37423 s i)) at 1.
  unfold R.v37423, N.v37423.
  unfold R.v16484, N.v16484.
  rewrite ?node_37422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37424 (s : N.State) (i : N.Inputs) :
  R.v37424 (state s) (inputs i) = Zmod.unsigned (N.v37424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37424 s i)) at 1.
  unfold R.v37424, N.v37424.
  rewrite ?node_37418.
  rewrite ?node_37419.
  rewrite ?node_37420.
  rewrite ?node_37423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37425 (s : N.State) (i : N.Inputs) :
  R.v37425 (state s) (inputs i) = Zmod.unsigned (N.v37425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37425 s i)) at 1.
  unfold R.v37425, N.v37425.
  unfold R.v6, N.v6.
  rewrite ?node_37424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37426 (s : N.State) (i : N.Inputs) :
  R.v37426 (state s) (inputs i) = Zmod.unsigned (N.v37426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37426 s i)) at 1.
  unfold R.v37426, N.v37426.
  rewrite ?node_16012.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37427 (s : N.State) (i : N.Inputs) :
  R.v37427 (state s) (inputs i) = Zmod.unsigned (N.v37427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37427 s i)) at 1.
  unfold R.v37427, N.v37427.
  unfold R.v6, N.v6.
  rewrite ?node_16040.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37428 (s : N.State) (i : N.Inputs) :
  R.v37428 (state s) (inputs i) = Zmod.unsigned (N.v37428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37428 s i)) at 1.
  unfold R.v37428, N.v37428.
  unfold R.v6, N.v6.
  rewrite ?node_16045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37429 (s : N.State) (i : N.Inputs) :
  R.v37429 (state s) (inputs i) = Zmod.unsigned (N.v37429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37429 s i)) at 1.
  unfold R.v37429, N.v37429.
  rewrite ?node_37426.
  rewrite ?node_37427.
  rewrite ?node_37428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37430 (s : N.State) (i : N.Inputs) :
  R.v37430 (state s) (inputs i) = Zmod.unsigned (N.v37430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37430 s i)) at 1.
  unfold R.v37430, N.v37430.
  rewrite ?node_37425.
  rewrite ?node_37429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37431 (s : N.State) (i : N.Inputs) :
  R.v37431 (state s) (inputs i) = Zmod.unsigned (N.v37431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37431 s i)) at 1.
  unfold R.v37431, N.v37431.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37432 (s : N.State) (i : N.Inputs) :
  R.v37432 (state s) (inputs i) = Zmod.unsigned (N.v37432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37432 s i)) at 1.
  unfold R.v37432, N.v37432.
  unfold R.v16463, N.v16463.
  rewrite !state_r2250_nr_5F2277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2250_nr_5F2277 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37433 (s : N.State) (i : N.Inputs) :
  R.v37433 (state s) (inputs i) = Zmod.unsigned (N.v37433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37433 s i)) at 1.
  unfold R.v37433, N.v37433.
  unfold R.v6, N.v6.
  rewrite !state_r2249_nr_5F2276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2249_nr_5F2276 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37434 (s : N.State) (i : N.Inputs) :
  R.v37434 (state s) (inputs i) = Zmod.unsigned (N.v37434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37434 s i)) at 1.
  unfold R.v37434, N.v37434.
  unfold R.v19, N.v19.
  rewrite ?node_37433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37435 (s : N.State) (i : N.Inputs) :
  R.v37435 (state s) (inputs i) = Zmod.unsigned (N.v37435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37435 s i)) at 1.
  unfold R.v37435, N.v37435.
  unfold R.v16484, N.v16484.
  rewrite ?node_37434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37436 (s : N.State) (i : N.Inputs) :
  R.v37436 (state s) (inputs i) = Zmod.unsigned (N.v37436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37436 s i)) at 1.
  unfold R.v37436, N.v37436.
  rewrite ?node_37432.
  rewrite ?node_37435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37437 (s : N.State) (i : N.Inputs) :
  R.v37437 (state s) (inputs i) = Zmod.unsigned (N.v37437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37437 s i)) at 1.
  unfold R.v37437, N.v37437.
  unfold R.v6, N.v6.
  rewrite ?node_37436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37438 (s : N.State) (i : N.Inputs) :
  R.v37438 (state s) (inputs i) = Zmod.unsigned (N.v37438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37438 s i)) at 1.
  unfold R.v37438, N.v37438.
  rewrite ?node_16007.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37439 (s : N.State) (i : N.Inputs) :
  R.v37439 (state s) (inputs i) = Zmod.unsigned (N.v37439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37439 s i)) at 1.
  unfold R.v37439, N.v37439.
  unfold R.v6, N.v6.
  rewrite ?node_16040.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37440 (s : N.State) (i : N.Inputs) :
  R.v37440 (state s) (inputs i) = Zmod.unsigned (N.v37440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37440 s i)) at 1.
  unfold R.v37440, N.v37440.
  rewrite ?node_37438.
  rewrite ?node_37439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37441 (s : N.State) (i : N.Inputs) :
  R.v37441 (state s) (inputs i) = Zmod.unsigned (N.v37441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37441 s i)) at 1.
  unfold R.v37441, N.v37441.
  rewrite ?node_37437.
  rewrite ?node_37440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37442 (s : N.State) (i : N.Inputs) :
  R.v37442 (state s) (inputs i) = Zmod.unsigned (N.v37442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37442 s i)) at 1.
  unfold R.v37442, N.v37442.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37443 (s : N.State) (i : N.Inputs) :
  R.v37443 (state s) (inputs i) = Zmod.unsigned (N.v37443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37443 s i)) at 1.
  unfold R.v37443, N.v37443.
  rewrite ?node_16011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37444 (s : N.State) (i : N.Inputs) :
  R.v37444 (state s) (inputs i) = Zmod.unsigned (N.v37444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37444 s i)) at 1.
  unfold R.v37444, N.v37444.
  unfold R.v6, N.v6.
  rewrite !state_r2251_nr_5F2278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2251_nr_5F2278 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37445 (s : N.State) (i : N.Inputs) :
  R.v37445 (state s) (inputs i) = Zmod.unsigned (N.v37445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37445 s i)) at 1.
  unfold R.v37445, N.v37445.
  unfold R.v6, N.v6.
  rewrite ?node_16007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37446 (s : N.State) (i : N.Inputs) :
  R.v37446 (state s) (inputs i) = Zmod.unsigned (N.v37446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37446 s i)) at 1.
  unfold R.v37446, N.v37446.
  rewrite ?node_37444.
  rewrite ?node_37445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37447 (s : N.State) (i : N.Inputs) :
  R.v37447 (state s) (inputs i) = Zmod.unsigned (N.v37447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37447 s i)) at 1.
  unfold R.v37447, N.v37447.
  unfold R.v16484, N.v16484.
  rewrite ?node_37446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37448 (s : N.State) (i : N.Inputs) :
  R.v37448 (state s) (inputs i) = Zmod.unsigned (N.v37448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37448 s i)) at 1.
  unfold R.v37448, N.v37448.
  rewrite ?node_37443.
  rewrite ?node_37447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37449 (s : N.State) (i : N.Inputs) :
  R.v37449 (state s) (inputs i) = Zmod.unsigned (N.v37449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37449 s i)) at 1.
  unfold R.v37449, N.v37449.
  unfold R.v6, N.v6.
  rewrite ?node_37448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37450 (s : N.State) (i : N.Inputs) :
  R.v37450 (state s) (inputs i) = Zmod.unsigned (N.v37450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37450 s i)) at 1.
  unfold R.v37450, N.v37450.
  rewrite ?node_16012.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37451 (s : N.State) (i : N.Inputs) :
  R.v37451 (state s) (inputs i) = Zmod.unsigned (N.v37451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37451 s i)) at 1.
  unfold R.v37451, N.v37451.
  unfold R.v6, N.v6.
  rewrite ?node_16045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37452 (s : N.State) (i : N.Inputs) :
  R.v37452 (state s) (inputs i) = Zmod.unsigned (N.v37452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37452 s i)) at 1.
  unfold R.v37452, N.v37452.
  rewrite ?node_37450.
  rewrite ?node_37451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37453 (s : N.State) (i : N.Inputs) :
  R.v37453 (state s) (inputs i) = Zmod.unsigned (N.v37453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37453 s i)) at 1.
  unfold R.v37453, N.v37453.
  rewrite ?node_37449.
  rewrite ?node_37452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37454 (s : N.State) (i : N.Inputs) :
  R.v37454 (state s) (inputs i) = Zmod.unsigned (N.v37454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37454 s i)) at 1.
  unfold R.v37454, N.v37454.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37455 (s : N.State) (i : N.Inputs) :
  R.v37455 (state s) (inputs i) = Zmod.unsigned (N.v37455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37455 s i)) at 1.
  unfold R.v37455, N.v37455.
  unfold R.v6, N.v6.
  rewrite !state_r2253_nr_5F2280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2253_nr_5F2280 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37456 (s : N.State) (i : N.Inputs) :
  R.v37456 (state s) (inputs i) = Zmod.unsigned (N.v37456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37456 s i)) at 1.
  unfold R.v37456, N.v37456.
  unfold R.v6, N.v6.
  rewrite !state_r2252_nr_5F2279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2252_nr_5F2279 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37457 (s : N.State) (i : N.Inputs) :
  R.v37457 (state s) (inputs i) = Zmod.unsigned (N.v37457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37457 s i)) at 1.
  unfold R.v37457, N.v37457.
  rewrite ?node_37455.
  rewrite ?node_37456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37458 (s : N.State) (i : N.Inputs) :
  R.v37458 (state s) (inputs i) = Zmod.unsigned (N.v37458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37458 s i)) at 1.
  unfold R.v37458, N.v37458.
  unfold R.v16463, N.v16463.
  rewrite ?node_37457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37459 (s : N.State) (i : N.Inputs) :
  R.v37459 (state s) (inputs i) = Zmod.unsigned (N.v37459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37459 s i)) at 1.
  unfold R.v37459, N.v37459.
  rewrite ?node_16013.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37460 (s : N.State) (i : N.Inputs) :
  R.v37460 (state s) (inputs i) = Zmod.unsigned (N.v37460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37460 s i)) at 1.
  unfold R.v37460, N.v37460.
  unfold R.v6, N.v6.
  rewrite ?node_16047.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37461 (s : N.State) (i : N.Inputs) :
  R.v37461 (state s) (inputs i) = Zmod.unsigned (N.v37461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37461 s i)) at 1.
  unfold R.v37461, N.v37461.
  rewrite ?node_37459.
  rewrite ?node_37460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37462 (s : N.State) (i : N.Inputs) :
  R.v37462 (state s) (inputs i) = Zmod.unsigned (N.v37462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37462 s i)) at 1.
  unfold R.v37462, N.v37462.
  rewrite ?node_37458.
  rewrite ?node_37461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37463 (s : N.State) (i : N.Inputs) :
  R.v37463 (state s) (inputs i) = Zmod.unsigned (N.v37463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37463 s i)) at 1.
  unfold R.v37463, N.v37463.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37464 (s : N.State) (i : N.Inputs) :
  R.v37464 (state s) (inputs i) = Zmod.unsigned (N.v37464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37464 s i)) at 1.
  unfold R.v37464, N.v37464.
  rewrite ?node_16040.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37465 (s : N.State) (i : N.Inputs) :
  R.v37465 (state s) (inputs i) = Zmod.unsigned (N.v37465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37465 s i)) at 1.
  unfold R.v37465, N.v37465.
  unfold R.v16463, N.v16463.
  rewrite !state_r2257_nr_5F2284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2257_nr_5F2284 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37466 (s : N.State) (i : N.Inputs) :
  R.v37466 (state s) (inputs i) = Zmod.unsigned (N.v37466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37466 s i)) at 1.
  unfold R.v37466, N.v37466.
  unfold R.v16463, N.v16463.
  rewrite !state_r2256_nr_5F2283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2256_nr_5F2283 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37467 (s : N.State) (i : N.Inputs) :
  R.v37467 (state s) (inputs i) = Zmod.unsigned (N.v37467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37467 s i)) at 1.
  unfold R.v37467, N.v37467.
  unfold R.v6, N.v6.
  rewrite !state_r2255_nr_5F2282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2255_nr_5F2282 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37468 (s : N.State) (i : N.Inputs) :
  R.v37468 (state s) (inputs i) = Zmod.unsigned (N.v37468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37468 s i)) at 1.
  unfold R.v37468, N.v37468.
  unfold R.v6, N.v6.
  rewrite !state_r2254_nr_5F2281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2254_nr_5F2281 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37469 (s : N.State) (i : N.Inputs) :
  R.v37469 (state s) (inputs i) = Zmod.unsigned (N.v37469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37469 s i)) at 1.
  unfold R.v37469, N.v37469.
  rewrite ?node_37467.
  rewrite ?node_37468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37470 (s : N.State) (i : N.Inputs) :
  R.v37470 (state s) (inputs i) = Zmod.unsigned (N.v37470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37470 s i)) at 1.
  unfold R.v37470, N.v37470.
  unfold R.v16484, N.v16484.
  rewrite ?node_37469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37471 (s : N.State) (i : N.Inputs) :
  R.v37471 (state s) (inputs i) = Zmod.unsigned (N.v37471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37471 s i)) at 1.
  unfold R.v37471, N.v37471.
  rewrite ?node_37464.
  rewrite ?node_37465.
  rewrite ?node_37466.
  rewrite ?node_37470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37472 (s : N.State) (i : N.Inputs) :
  R.v37472 (state s) (inputs i) = Zmod.unsigned (N.v37472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37472 s i)) at 1.
  unfold R.v37472, N.v37472.
  unfold R.v6, N.v6.
  rewrite ?node_37471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37473 (s : N.State) (i : N.Inputs) :
  R.v37473 (state s) (inputs i) = Zmod.unsigned (N.v37473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37473 s i)) at 1.
  unfold R.v37473, N.v37473.
  rewrite ?node_16041.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37474 (s : N.State) (i : N.Inputs) :
  R.v37474 (state s) (inputs i) = Zmod.unsigned (N.v37474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37474 s i)) at 1.
  unfold R.v37474, N.v37474.
  unfold R.v6, N.v6.
  rewrite ?node_16069.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37475 (s : N.State) (i : N.Inputs) :
  R.v37475 (state s) (inputs i) = Zmod.unsigned (N.v37475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37475 s i)) at 1.
  unfold R.v37475, N.v37475.
  unfold R.v6, N.v6.
  rewrite ?node_16074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37476 (s : N.State) (i : N.Inputs) :
  R.v37476 (state s) (inputs i) = Zmod.unsigned (N.v37476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37476 s i)) at 1.
  unfold R.v37476, N.v37476.
  rewrite ?node_37473.
  rewrite ?node_37474.
  rewrite ?node_37475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37477 (s : N.State) (i : N.Inputs) :
  R.v37477 (state s) (inputs i) = Zmod.unsigned (N.v37477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37477 s i)) at 1.
  unfold R.v37477, N.v37477.
  rewrite ?node_37472.
  rewrite ?node_37476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37478 (s : N.State) (i : N.Inputs) :
  R.v37478 (state s) (inputs i) = Zmod.unsigned (N.v37478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37478 s i)) at 1.
  unfold R.v37478, N.v37478.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37479 (s : N.State) (i : N.Inputs) :
  R.v37479 (state s) (inputs i) = Zmod.unsigned (N.v37479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37479 s i)) at 1.
  unfold R.v37479, N.v37479.
  unfold R.v16463, N.v16463.
  rewrite !state_r2256_nr_5F2283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2256_nr_5F2283 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37480 (s : N.State) (i : N.Inputs) :
  R.v37480 (state s) (inputs i) = Zmod.unsigned (N.v37480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37480 s i)) at 1.
  unfold R.v37480, N.v37480.
  unfold R.v6, N.v6.
  rewrite !state_r2255_nr_5F2282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2255_nr_5F2282 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37481 (s : N.State) (i : N.Inputs) :
  R.v37481 (state s) (inputs i) = Zmod.unsigned (N.v37481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37481 s i)) at 1.
  unfold R.v37481, N.v37481.
  unfold R.v6, N.v6.
  rewrite !state_r2254_nr_5F2281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2254_nr_5F2281 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37482 (s : N.State) (i : N.Inputs) :
  R.v37482 (state s) (inputs i) = Zmod.unsigned (N.v37482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37482 s i)) at 1.
  unfold R.v37482, N.v37482.
  rewrite ?node_37480.
  rewrite ?node_37481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37483 (s : N.State) (i : N.Inputs) :
  R.v37483 (state s) (inputs i) = Zmod.unsigned (N.v37483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37483 s i)) at 1.
  unfold R.v37483, N.v37483.
  unfold R.v16484, N.v16484.
  rewrite ?node_37482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37484 (s : N.State) (i : N.Inputs) :
  R.v37484 (state s) (inputs i) = Zmod.unsigned (N.v37484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37484 s i)) at 1.
  unfold R.v37484, N.v37484.
  rewrite ?node_37479.
  rewrite ?node_37483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37485 (s : N.State) (i : N.Inputs) :
  R.v37485 (state s) (inputs i) = Zmod.unsigned (N.v37485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37485 s i)) at 1.
  unfold R.v37485, N.v37485.
  unfold R.v6, N.v6.
  rewrite ?node_37484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37486 (s : N.State) (i : N.Inputs) :
  R.v37486 (state s) (inputs i) = Zmod.unsigned (N.v37486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37486 s i)) at 1.
  unfold R.v37486, N.v37486.
  rewrite ?node_16037.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37487 (s : N.State) (i : N.Inputs) :
  R.v37487 (state s) (inputs i) = Zmod.unsigned (N.v37487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37487 s i)) at 1.
  unfold R.v37487, N.v37487.
  unfold R.v6, N.v6.
  rewrite ?node_16069.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37488 (s : N.State) (i : N.Inputs) :
  R.v37488 (state s) (inputs i) = Zmod.unsigned (N.v37488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37488 s i)) at 1.
  unfold R.v37488, N.v37488.
  rewrite ?node_37486.
  rewrite ?node_37487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37489 (s : N.State) (i : N.Inputs) :
  R.v37489 (state s) (inputs i) = Zmod.unsigned (N.v37489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37489 s i)) at 1.
  unfold R.v37489, N.v37489.
  rewrite ?node_37485.
  rewrite ?node_37488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37490 (s : N.State) (i : N.Inputs) :
  R.v37490 (state s) (inputs i) = Zmod.unsigned (N.v37490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37490 s i)) at 1.
  unfold R.v37490, N.v37490.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37491 (s : N.State) (i : N.Inputs) :
  R.v37491 (state s) (inputs i) = Zmod.unsigned (N.v37491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37491 s i)) at 1.
  unfold R.v37491, N.v37491.
  rewrite ?node_16040.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37492 (s : N.State) (i : N.Inputs) :
  R.v37492 (state s) (inputs i) = Zmod.unsigned (N.v37492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37492 s i)) at 1.
  unfold R.v37492, N.v37492.
  unfold R.v6, N.v6.
  rewrite !state_r2257_nr_5F2284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2257_nr_5F2284 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37493 (s : N.State) (i : N.Inputs) :
  R.v37493 (state s) (inputs i) = Zmod.unsigned (N.v37493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37493 s i)) at 1.
  unfold R.v37493, N.v37493.
  unfold R.v6, N.v6.
  rewrite ?node_16037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37494 (s : N.State) (i : N.Inputs) :
  R.v37494 (state s) (inputs i) = Zmod.unsigned (N.v37494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37494 s i)) at 1.
  unfold R.v37494, N.v37494.
  rewrite ?node_37492.
  rewrite ?node_37493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37495 (s : N.State) (i : N.Inputs) :
  R.v37495 (state s) (inputs i) = Zmod.unsigned (N.v37495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37495 s i)) at 1.
  unfold R.v37495, N.v37495.
  unfold R.v16484, N.v16484.
  rewrite ?node_37494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37496 (s : N.State) (i : N.Inputs) :
  R.v37496 (state s) (inputs i) = Zmod.unsigned (N.v37496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37496 s i)) at 1.
  unfold R.v37496, N.v37496.
  rewrite ?node_37491.
  rewrite ?node_37495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37497 (s : N.State) (i : N.Inputs) :
  R.v37497 (state s) (inputs i) = Zmod.unsigned (N.v37497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37497 s i)) at 1.
  unfold R.v37497, N.v37497.
  unfold R.v6, N.v6.
  rewrite ?node_37496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37498 (s : N.State) (i : N.Inputs) :
  R.v37498 (state s) (inputs i) = Zmod.unsigned (N.v37498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37498 s i)) at 1.
  unfold R.v37498, N.v37498.
  rewrite ?node_16041.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37499 (s : N.State) (i : N.Inputs) :
  R.v37499 (state s) (inputs i) = Zmod.unsigned (N.v37499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37499 s i)) at 1.
  unfold R.v37499, N.v37499.
  unfold R.v6, N.v6.
  rewrite ?node_16074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37500 (s : N.State) (i : N.Inputs) :
  R.v37500 (state s) (inputs i) = Zmod.unsigned (N.v37500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37500 s i)) at 1.
  unfold R.v37500, N.v37500.
  rewrite ?node_37498.
  rewrite ?node_37499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37501 (s : N.State) (i : N.Inputs) :
  R.v37501 (state s) (inputs i) = Zmod.unsigned (N.v37501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37501 s i)) at 1.
  unfold R.v37501, N.v37501.
  rewrite ?node_37497.
  rewrite ?node_37500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37502 (s : N.State) (i : N.Inputs) :
  R.v37502 (state s) (inputs i) = Zmod.unsigned (N.v37502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37502 s i)) at 1.
  unfold R.v37502, N.v37502.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37503 (s : N.State) (i : N.Inputs) :
  R.v37503 (state s) (inputs i) = Zmod.unsigned (N.v37503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37503 s i)) at 1.
  unfold R.v37503, N.v37503.
  rewrite ?node_16069.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37504 (s : N.State) (i : N.Inputs) :
  R.v37504 (state s) (inputs i) = Zmod.unsigned (N.v37504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37504 s i)) at 1.
  unfold R.v37504, N.v37504.
  unfold R.v16463, N.v16463.
  rewrite !state_r2261_nr_5F2289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2261_nr_5F2289 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37505 (s : N.State) (i : N.Inputs) :
  R.v37505 (state s) (inputs i) = Zmod.unsigned (N.v37505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37505 s i)) at 1.
  unfold R.v37505, N.v37505.
  unfold R.v16463, N.v16463.
  rewrite !state_r2260_nr_5F2288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2260_nr_5F2288 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37506 (s : N.State) (i : N.Inputs) :
  R.v37506 (state s) (inputs i) = Zmod.unsigned (N.v37506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37506 s i)) at 1.
  unfold R.v37506, N.v37506.
  unfold R.v6, N.v6.
  rewrite !state_r2259_nr_5F2287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2259_nr_5F2287 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37507 (s : N.State) (i : N.Inputs) :
  R.v37507 (state s) (inputs i) = Zmod.unsigned (N.v37507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37507 s i)) at 1.
  unfold R.v37507, N.v37507.
  unfold R.v19, N.v19.
  rewrite ?node_37506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37508 (s : N.State) (i : N.Inputs) :
  R.v37508 (state s) (inputs i) = Zmod.unsigned (N.v37508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37508 s i)) at 1.
  unfold R.v37508, N.v37508.
  unfold R.v16484, N.v16484.
  rewrite ?node_37507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37509 (s : N.State) (i : N.Inputs) :
  R.v37509 (state s) (inputs i) = Zmod.unsigned (N.v37509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37509 s i)) at 1.
  unfold R.v37509, N.v37509.
  rewrite ?node_37503.
  rewrite ?node_37504.
  rewrite ?node_37505.
  rewrite ?node_37508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37510 (s : N.State) (i : N.Inputs) :
  R.v37510 (state s) (inputs i) = Zmod.unsigned (N.v37510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37510 s i)) at 1.
  unfold R.v37510, N.v37510.
  unfold R.v6, N.v6.
  rewrite ?node_37509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37511 (s : N.State) (i : N.Inputs) :
  R.v37511 (state s) (inputs i) = Zmod.unsigned (N.v37511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37511 s i)) at 1.
  unfold R.v37511, N.v37511.
  rewrite ?node_16070.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37512 (s : N.State) (i : N.Inputs) :
  R.v37512 (state s) (inputs i) = Zmod.unsigned (N.v37512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37512 s i)) at 1.
  unfold R.v37512, N.v37512.
  unfold R.v6, N.v6.
  rewrite ?node_16095.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37513 (s : N.State) (i : N.Inputs) :
  R.v37513 (state s) (inputs i) = Zmod.unsigned (N.v37513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37513 s i)) at 1.
  unfold R.v37513, N.v37513.
  unfold R.v6, N.v6.
  rewrite ?node_16099.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37514 (s : N.State) (i : N.Inputs) :
  R.v37514 (state s) (inputs i) = Zmod.unsigned (N.v37514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37514 s i)) at 1.
  unfold R.v37514, N.v37514.
  rewrite ?node_37511.
  rewrite ?node_37512.
  rewrite ?node_37513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37515 (s : N.State) (i : N.Inputs) :
  R.v37515 (state s) (inputs i) = Zmod.unsigned (N.v37515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37515 s i)) at 1.
  unfold R.v37515, N.v37515.
  rewrite ?node_37510.
  rewrite ?node_37514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37516 (s : N.State) (i : N.Inputs) :
  R.v37516 (state s) (inputs i) = Zmod.unsigned (N.v37516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37516 s i)) at 1.
  unfold R.v37516, N.v37516.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37517 (s : N.State) (i : N.Inputs) :
  R.v37517 (state s) (inputs i) = Zmod.unsigned (N.v37517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37517 s i)) at 1.
  unfold R.v37517, N.v37517.
  unfold R.v16463, N.v16463.
  rewrite !state_r2260_nr_5F2288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2260_nr_5F2288 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37518 (s : N.State) (i : N.Inputs) :
  R.v37518 (state s) (inputs i) = Zmod.unsigned (N.v37518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37518 s i)) at 1.
  unfold R.v37518, N.v37518.
  unfold R.v6, N.v6.
  rewrite !state_r2259_nr_5F2287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2259_nr_5F2287 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37519 (s : N.State) (i : N.Inputs) :
  R.v37519 (state s) (inputs i) = Zmod.unsigned (N.v37519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37519 s i)) at 1.
  unfold R.v37519, N.v37519.
  unfold R.v19, N.v19.
  rewrite ?node_37518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37520 (s : N.State) (i : N.Inputs) :
  R.v37520 (state s) (inputs i) = Zmod.unsigned (N.v37520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37520 s i)) at 1.
  unfold R.v37520, N.v37520.
  unfold R.v16484, N.v16484.
  rewrite ?node_37519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37521 (s : N.State) (i : N.Inputs) :
  R.v37521 (state s) (inputs i) = Zmod.unsigned (N.v37521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37521 s i)) at 1.
  unfold R.v37521, N.v37521.
  rewrite ?node_37517.
  rewrite ?node_37520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37522 (s : N.State) (i : N.Inputs) :
  R.v37522 (state s) (inputs i) = Zmod.unsigned (N.v37522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37522 s i)) at 1.
  unfold R.v37522, N.v37522.
  unfold R.v6, N.v6.
  rewrite ?node_37521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37523 (s : N.State) (i : N.Inputs) :
  R.v37523 (state s) (inputs i) = Zmod.unsigned (N.v37523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37523 s i)) at 1.
  unfold R.v37523, N.v37523.
  rewrite ?node_16065.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37524 (s : N.State) (i : N.Inputs) :
  R.v37524 (state s) (inputs i) = Zmod.unsigned (N.v37524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37524 s i)) at 1.
  unfold R.v37524, N.v37524.
  unfold R.v6, N.v6.
  rewrite ?node_16095.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37525 (s : N.State) (i : N.Inputs) :
  R.v37525 (state s) (inputs i) = Zmod.unsigned (N.v37525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37525 s i)) at 1.
  unfold R.v37525, N.v37525.
  rewrite ?node_37523.
  rewrite ?node_37524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37526 (s : N.State) (i : N.Inputs) :
  R.v37526 (state s) (inputs i) = Zmod.unsigned (N.v37526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37526 s i)) at 1.
  unfold R.v37526, N.v37526.
  rewrite ?node_37522.
  rewrite ?node_37525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37527 (s : N.State) (i : N.Inputs) :
  R.v37527 (state s) (inputs i) = Zmod.unsigned (N.v37527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37527 s i)) at 1.
  unfold R.v37527, N.v37527.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37528 (s : N.State) (i : N.Inputs) :
  R.v37528 (state s) (inputs i) = Zmod.unsigned (N.v37528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37528 s i)) at 1.
  unfold R.v37528, N.v37528.
  rewrite ?node_16069.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37529 (s : N.State) (i : N.Inputs) :
  R.v37529 (state s) (inputs i) = Zmod.unsigned (N.v37529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37529 s i)) at 1.
  unfold R.v37529, N.v37529.
  unfold R.v6, N.v6.
  rewrite !state_r2261_nr_5F2289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2261_nr_5F2289 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37530 (s : N.State) (i : N.Inputs) :
  R.v37530 (state s) (inputs i) = Zmod.unsigned (N.v37530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37530 s i)) at 1.
  unfold R.v37530, N.v37530.
  unfold R.v6, N.v6.
  rewrite ?node_16065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37531 (s : N.State) (i : N.Inputs) :
  R.v37531 (state s) (inputs i) = Zmod.unsigned (N.v37531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37531 s i)) at 1.
  unfold R.v37531, N.v37531.
  rewrite ?node_37529.
  rewrite ?node_37530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37532 (s : N.State) (i : N.Inputs) :
  R.v37532 (state s) (inputs i) = Zmod.unsigned (N.v37532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37532 s i)) at 1.
  unfold R.v37532, N.v37532.
  unfold R.v16484, N.v16484.
  rewrite ?node_37531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37533 (s : N.State) (i : N.Inputs) :
  R.v37533 (state s) (inputs i) = Zmod.unsigned (N.v37533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37533 s i)) at 1.
  unfold R.v37533, N.v37533.
  rewrite ?node_37528.
  rewrite ?node_37532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37534 (s : N.State) (i : N.Inputs) :
  R.v37534 (state s) (inputs i) = Zmod.unsigned (N.v37534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37534 s i)) at 1.
  unfold R.v37534, N.v37534.
  unfold R.v6, N.v6.
  rewrite ?node_37533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37535 (s : N.State) (i : N.Inputs) :
  R.v37535 (state s) (inputs i) = Zmod.unsigned (N.v37535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37535 s i)) at 1.
  unfold R.v37535, N.v37535.
  rewrite ?node_16070.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37536 (s : N.State) (i : N.Inputs) :
  R.v37536 (state s) (inputs i) = Zmod.unsigned (N.v37536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37536 s i)) at 1.
  unfold R.v37536, N.v37536.
  unfold R.v6, N.v6.
  rewrite ?node_16099.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37537 (s : N.State) (i : N.Inputs) :
  R.v37537 (state s) (inputs i) = Zmod.unsigned (N.v37537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37537 s i)) at 1.
  unfold R.v37537, N.v37537.
  rewrite ?node_37535.
  rewrite ?node_37536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37538 (s : N.State) (i : N.Inputs) :
  R.v37538 (state s) (inputs i) = Zmod.unsigned (N.v37538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37538 s i)) at 1.
  unfold R.v37538, N.v37538.
  rewrite ?node_37534.
  rewrite ?node_37537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37539 (s : N.State) (i : N.Inputs) :
  R.v37539 (state s) (inputs i) = Zmod.unsigned (N.v37539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37539 s i)) at 1.
  unfold R.v37539, N.v37539.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37540 (s : N.State) (i : N.Inputs) :
  R.v37540 (state s) (inputs i) = Zmod.unsigned (N.v37540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37540 s i)) at 1.
  unfold R.v37540, N.v37540.
  rewrite ?node_16095.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37541 (s : N.State) (i : N.Inputs) :
  R.v37541 (state s) (inputs i) = Zmod.unsigned (N.v37541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37541 s i)) at 1.
  unfold R.v37541, N.v37541.
  unfold R.v16463, N.v16463.
  rewrite !state_r2266_nr_5F2294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2266_nr_5F2294 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37542 (s : N.State) (i : N.Inputs) :
  R.v37542 (state s) (inputs i) = Zmod.unsigned (N.v37542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37542 s i)) at 1.
  unfold R.v37542, N.v37542.
  unfold R.v16463, N.v16463.
  rewrite !state_r2265_nr_5F2293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2265_nr_5F2293 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37543 (s : N.State) (i : N.Inputs) :
  R.v37543 (state s) (inputs i) = Zmod.unsigned (N.v37543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37543 s i)) at 1.
  unfold R.v37543, N.v37543.
  unfold R.v6, N.v6.
  rewrite !state_r2264_nr_5F2292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2264_nr_5F2292 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37544 (s : N.State) (i : N.Inputs) :
  R.v37544 (state s) (inputs i) = Zmod.unsigned (N.v37544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37544 s i)) at 1.
  unfold R.v37544, N.v37544.
  unfold R.v6, N.v6.
  rewrite !state_r2263_nr_5F2291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2263_nr_5F2291 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37545 (s : N.State) (i : N.Inputs) :
  R.v37545 (state s) (inputs i) = Zmod.unsigned (N.v37545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37545 s i)) at 1.
  unfold R.v37545, N.v37545.
  rewrite ?node_37543.
  rewrite ?node_37544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37546 (s : N.State) (i : N.Inputs) :
  R.v37546 (state s) (inputs i) = Zmod.unsigned (N.v37546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37546 s i)) at 1.
  unfold R.v37546, N.v37546.
  unfold R.v16484, N.v16484.
  rewrite ?node_37545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37547 (s : N.State) (i : N.Inputs) :
  R.v37547 (state s) (inputs i) = Zmod.unsigned (N.v37547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37547 s i)) at 1.
  unfold R.v37547, N.v37547.
  rewrite ?node_37540.
  rewrite ?node_37541.
  rewrite ?node_37542.
  rewrite ?node_37546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37548 (s : N.State) (i : N.Inputs) :
  R.v37548 (state s) (inputs i) = Zmod.unsigned (N.v37548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37548 s i)) at 1.
  unfold R.v37548, N.v37548.
  unfold R.v6, N.v6.
  rewrite ?node_37547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37549 (s : N.State) (i : N.Inputs) :
  R.v37549 (state s) (inputs i) = Zmod.unsigned (N.v37549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37549 s i)) at 1.
  unfold R.v37549, N.v37549.
  rewrite ?node_16096.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37550 (s : N.State) (i : N.Inputs) :
  R.v37550 (state s) (inputs i) = Zmod.unsigned (N.v37550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37550 s i)) at 1.
  unfold R.v37550, N.v37550.
  unfold R.v6, N.v6.
  rewrite ?node_16119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37551 (s : N.State) (i : N.Inputs) :
  R.v37551 (state s) (inputs i) = Zmod.unsigned (N.v37551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37551 s i)) at 1.
  unfold R.v37551, N.v37551.
  unfold R.v6, N.v6.
  rewrite ?node_16123.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37552 (s : N.State) (i : N.Inputs) :
  R.v37552 (state s) (inputs i) = Zmod.unsigned (N.v37552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37552 s i)) at 1.
  unfold R.v37552, N.v37552.
  rewrite ?node_37549.
  rewrite ?node_37550.
  rewrite ?node_37551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37553 (s : N.State) (i : N.Inputs) :
  R.v37553 (state s) (inputs i) = Zmod.unsigned (N.v37553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37553 s i)) at 1.
  unfold R.v37553, N.v37553.
  rewrite ?node_37548.
  rewrite ?node_37552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37554 (s : N.State) (i : N.Inputs) :
  R.v37554 (state s) (inputs i) = Zmod.unsigned (N.v37554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37554 s i)) at 1.
  unfold R.v37554, N.v37554.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37555 (s : N.State) (i : N.Inputs) :
  R.v37555 (state s) (inputs i) = Zmod.unsigned (N.v37555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37555 s i)) at 1.
  unfold R.v37555, N.v37555.
  unfold R.v16463, N.v16463.
  rewrite !state_r2265_nr_5F2293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2265_nr_5F2293 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37556 (s : N.State) (i : N.Inputs) :
  R.v37556 (state s) (inputs i) = Zmod.unsigned (N.v37556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37556 s i)) at 1.
  unfold R.v37556, N.v37556.
  unfold R.v6, N.v6.
  rewrite !state_r2264_nr_5F2292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2264_nr_5F2292 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37557 (s : N.State) (i : N.Inputs) :
  R.v37557 (state s) (inputs i) = Zmod.unsigned (N.v37557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37557 s i)) at 1.
  unfold R.v37557, N.v37557.
  unfold R.v6, N.v6.
  rewrite !state_r2263_nr_5F2291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2263_nr_5F2291 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37558 (s : N.State) (i : N.Inputs) :
  R.v37558 (state s) (inputs i) = Zmod.unsigned (N.v37558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37558 s i)) at 1.
  unfold R.v37558, N.v37558.
  rewrite ?node_37556.
  rewrite ?node_37557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37559 (s : N.State) (i : N.Inputs) :
  R.v37559 (state s) (inputs i) = Zmod.unsigned (N.v37559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37559 s i)) at 1.
  unfold R.v37559, N.v37559.
  unfold R.v16484, N.v16484.
  rewrite ?node_37558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37560 (s : N.State) (i : N.Inputs) :
  R.v37560 (state s) (inputs i) = Zmod.unsigned (N.v37560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37560 s i)) at 1.
  unfold R.v37560, N.v37560.
  rewrite ?node_37555.
  rewrite ?node_37559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37561 (s : N.State) (i : N.Inputs) :
  R.v37561 (state s) (inputs i) = Zmod.unsigned (N.v37561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37561 s i)) at 1.
  unfold R.v37561, N.v37561.
  unfold R.v6, N.v6.
  rewrite ?node_37560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37562 (s : N.State) (i : N.Inputs) :
  R.v37562 (state s) (inputs i) = Zmod.unsigned (N.v37562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37562 s i)) at 1.
  unfold R.v37562, N.v37562.
  rewrite ?node_16092.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37563 (s : N.State) (i : N.Inputs) :
  R.v37563 (state s) (inputs i) = Zmod.unsigned (N.v37563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37563 s i)) at 1.
  unfold R.v37563, N.v37563.
  unfold R.v6, N.v6.
  rewrite ?node_16119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37564 (s : N.State) (i : N.Inputs) :
  R.v37564 (state s) (inputs i) = Zmod.unsigned (N.v37564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37564 s i)) at 1.
  unfold R.v37564, N.v37564.
  rewrite ?node_37562.
  rewrite ?node_37563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37565 (s : N.State) (i : N.Inputs) :
  R.v37565 (state s) (inputs i) = Zmod.unsigned (N.v37565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37565 s i)) at 1.
  unfold R.v37565, N.v37565.
  rewrite ?node_37561.
  rewrite ?node_37564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37566 (s : N.State) (i : N.Inputs) :
  R.v37566 (state s) (inputs i) = Zmod.unsigned (N.v37566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37566 s i)) at 1.
  unfold R.v37566, N.v37566.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37567 (s : N.State) (i : N.Inputs) :
  R.v37567 (state s) (inputs i) = Zmod.unsigned (N.v37567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37567 s i)) at 1.
  unfold R.v37567, N.v37567.
  rewrite ?node_16095.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37568 (s : N.State) (i : N.Inputs) :
  R.v37568 (state s) (inputs i) = Zmod.unsigned (N.v37568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37568 s i)) at 1.
  unfold R.v37568, N.v37568.
  unfold R.v6, N.v6.
  rewrite !state_r2266_nr_5F2294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2266_nr_5F2294 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37569 (s : N.State) (i : N.Inputs) :
  R.v37569 (state s) (inputs i) = Zmod.unsigned (N.v37569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37569 s i)) at 1.
  unfold R.v37569, N.v37569.
  unfold R.v6, N.v6.
  rewrite ?node_16092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37570 (s : N.State) (i : N.Inputs) :
  R.v37570 (state s) (inputs i) = Zmod.unsigned (N.v37570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37570 s i)) at 1.
  unfold R.v37570, N.v37570.
  rewrite ?node_37568.
  rewrite ?node_37569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37571 (s : N.State) (i : N.Inputs) :
  R.v37571 (state s) (inputs i) = Zmod.unsigned (N.v37571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37571 s i)) at 1.
  unfold R.v37571, N.v37571.
  unfold R.v16484, N.v16484.
  rewrite ?node_37570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37572 (s : N.State) (i : N.Inputs) :
  R.v37572 (state s) (inputs i) = Zmod.unsigned (N.v37572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37572 s i)) at 1.
  unfold R.v37572, N.v37572.
  rewrite ?node_37567.
  rewrite ?node_37571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37573 (s : N.State) (i : N.Inputs) :
  R.v37573 (state s) (inputs i) = Zmod.unsigned (N.v37573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37573 s i)) at 1.
  unfold R.v37573, N.v37573.
  unfold R.v6, N.v6.
  rewrite ?node_37572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37574 (s : N.State) (i : N.Inputs) :
  R.v37574 (state s) (inputs i) = Zmod.unsigned (N.v37574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37574 s i)) at 1.
  unfold R.v37574, N.v37574.
  rewrite ?node_16096.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37575 (s : N.State) (i : N.Inputs) :
  R.v37575 (state s) (inputs i) = Zmod.unsigned (N.v37575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37575 s i)) at 1.
  unfold R.v37575, N.v37575.
  unfold R.v6, N.v6.
  rewrite ?node_16123.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37576 (s : N.State) (i : N.Inputs) :
  R.v37576 (state s) (inputs i) = Zmod.unsigned (N.v37576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37576 s i)) at 1.
  unfold R.v37576, N.v37576.
  rewrite ?node_37574.
  rewrite ?node_37575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37577 (s : N.State) (i : N.Inputs) :
  R.v37577 (state s) (inputs i) = Zmod.unsigned (N.v37577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37577 s i)) at 1.
  unfold R.v37577, N.v37577.
  rewrite ?node_37573.
  rewrite ?node_37576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37578 (s : N.State) (i : N.Inputs) :
  R.v37578 (state s) (inputs i) = Zmod.unsigned (N.v37578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37578 s i)) at 1.
  unfold R.v37578, N.v37578.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37579 (s : N.State) (i : N.Inputs) :
  R.v37579 (state s) (inputs i) = Zmod.unsigned (N.v37579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37579 s i)) at 1.
  unfold R.v37579, N.v37579.
  rewrite ?node_16119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37580 (s : N.State) (i : N.Inputs) :
  R.v37580 (state s) (inputs i) = Zmod.unsigned (N.v37580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37580 s i)) at 1.
  unfold R.v37580, N.v37580.
  unfold R.v16463, N.v16463.
  rewrite !state_r2269_nr_5F2298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2269_nr_5F2298 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37581 (s : N.State) (i : N.Inputs) :
  R.v37581 (state s) (inputs i) = Zmod.unsigned (N.v37581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37581 s i)) at 1.
  unfold R.v37581, N.v37581.
  unfold R.v16463, N.v16463.
  rewrite !state_r2268_nr_5F2297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2268_nr_5F2297 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37582 (s : N.State) (i : N.Inputs) :
  R.v37582 (state s) (inputs i) = Zmod.unsigned (N.v37582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37582 s i)) at 1.
  unfold R.v37582, N.v37582.
  unfold R.v6, N.v6.
  rewrite !state_r2267_nr_5F2296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2267_nr_5F2296 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37583 (s : N.State) (i : N.Inputs) :
  R.v37583 (state s) (inputs i) = Zmod.unsigned (N.v37583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37583 s i)) at 1.
  unfold R.v37583, N.v37583.
  unfold R.v19, N.v19.
  rewrite ?node_37582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37584 (s : N.State) (i : N.Inputs) :
  R.v37584 (state s) (inputs i) = Zmod.unsigned (N.v37584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37584 s i)) at 1.
  unfold R.v37584, N.v37584.
  unfold R.v16484, N.v16484.
  rewrite ?node_37583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37585 (s : N.State) (i : N.Inputs) :
  R.v37585 (state s) (inputs i) = Zmod.unsigned (N.v37585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37585 s i)) at 1.
  unfold R.v37585, N.v37585.
  rewrite ?node_37579.
  rewrite ?node_37580.
  rewrite ?node_37581.
  rewrite ?node_37584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37586 (s : N.State) (i : N.Inputs) :
  R.v37586 (state s) (inputs i) = Zmod.unsigned (N.v37586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37586 s i)) at 1.
  unfold R.v37586, N.v37586.
  unfold R.v6, N.v6.
  rewrite ?node_37585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37587 (s : N.State) (i : N.Inputs) :
  R.v37587 (state s) (inputs i) = Zmod.unsigned (N.v37587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37587 s i)) at 1.
  unfold R.v37587, N.v37587.
  rewrite ?node_16120.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37588 (s : N.State) (i : N.Inputs) :
  R.v37588 (state s) (inputs i) = Zmod.unsigned (N.v37588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37588 s i)) at 1.
  unfold R.v37588, N.v37588.
  unfold R.v6, N.v6.
  rewrite ?node_16137.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37589 (s : N.State) (i : N.Inputs) :
  R.v37589 (state s) (inputs i) = Zmod.unsigned (N.v37589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37589 s i)) at 1.
  unfold R.v37589, N.v37589.
  unfold R.v6, N.v6.
  rewrite ?node_16141.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37590 (s : N.State) (i : N.Inputs) :
  R.v37590 (state s) (inputs i) = Zmod.unsigned (N.v37590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37590 s i)) at 1.
  unfold R.v37590, N.v37590.
  rewrite ?node_37587.
  rewrite ?node_37588.
  rewrite ?node_37589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37591 (s : N.State) (i : N.Inputs) :
  R.v37591 (state s) (inputs i) = Zmod.unsigned (N.v37591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37591 s i)) at 1.
  unfold R.v37591, N.v37591.
  rewrite ?node_37586.
  rewrite ?node_37590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37592 (s : N.State) (i : N.Inputs) :
  R.v37592 (state s) (inputs i) = Zmod.unsigned (N.v37592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37592 s i)) at 1.
  unfold R.v37592, N.v37592.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37593 (s : N.State) (i : N.Inputs) :
  R.v37593 (state s) (inputs i) = Zmod.unsigned (N.v37593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37593 s i)) at 1.
  unfold R.v37593, N.v37593.
  unfold R.v16463, N.v16463.
  rewrite !state_r2268_nr_5F2297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2268_nr_5F2297 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37594 (s : N.State) (i : N.Inputs) :
  R.v37594 (state s) (inputs i) = Zmod.unsigned (N.v37594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37594 s i)) at 1.
  unfold R.v37594, N.v37594.
  unfold R.v6, N.v6.
  rewrite !state_r2267_nr_5F2296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2267_nr_5F2296 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37595 (s : N.State) (i : N.Inputs) :
  R.v37595 (state s) (inputs i) = Zmod.unsigned (N.v37595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37595 s i)) at 1.
  unfold R.v37595, N.v37595.
  unfold R.v19, N.v19.
  rewrite ?node_37594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37596 (s : N.State) (i : N.Inputs) :
  R.v37596 (state s) (inputs i) = Zmod.unsigned (N.v37596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37596 s i)) at 1.
  unfold R.v37596, N.v37596.
  unfold R.v16484, N.v16484.
  rewrite ?node_37595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37597 (s : N.State) (i : N.Inputs) :
  R.v37597 (state s) (inputs i) = Zmod.unsigned (N.v37597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37597 s i)) at 1.
  unfold R.v37597, N.v37597.
  rewrite ?node_37593.
  rewrite ?node_37596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37598 (s : N.State) (i : N.Inputs) :
  R.v37598 (state s) (inputs i) = Zmod.unsigned (N.v37598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37598 s i)) at 1.
  unfold R.v37598, N.v37598.
  unfold R.v6, N.v6.
  rewrite ?node_37597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37599 (s : N.State) (i : N.Inputs) :
  R.v37599 (state s) (inputs i) = Zmod.unsigned (N.v37599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37599 s i)) at 1.
  unfold R.v37599, N.v37599.
  rewrite ?node_16115.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37600 (s : N.State) (i : N.Inputs) :
  R.v37600 (state s) (inputs i) = Zmod.unsigned (N.v37600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37600 s i)) at 1.
  unfold R.v37600, N.v37600.
  unfold R.v6, N.v6.
  rewrite ?node_16137.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37601 (s : N.State) (i : N.Inputs) :
  R.v37601 (state s) (inputs i) = Zmod.unsigned (N.v37601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37601 s i)) at 1.
  unfold R.v37601, N.v37601.
  rewrite ?node_37599.
  rewrite ?node_37600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37602 (s : N.State) (i : N.Inputs) :
  R.v37602 (state s) (inputs i) = Zmod.unsigned (N.v37602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37602 s i)) at 1.
  unfold R.v37602, N.v37602.
  rewrite ?node_37598.
  rewrite ?node_37601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37603 (s : N.State) (i : N.Inputs) :
  R.v37603 (state s) (inputs i) = Zmod.unsigned (N.v37603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37603 s i)) at 1.
  unfold R.v37603, N.v37603.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37604 (s : N.State) (i : N.Inputs) :
  R.v37604 (state s) (inputs i) = Zmod.unsigned (N.v37604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37604 s i)) at 1.
  unfold R.v37604, N.v37604.
  rewrite ?node_16119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37605 (s : N.State) (i : N.Inputs) :
  R.v37605 (state s) (inputs i) = Zmod.unsigned (N.v37605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37605 s i)) at 1.
  unfold R.v37605, N.v37605.
  unfold R.v6, N.v6.
  rewrite !state_r2269_nr_5F2298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2269_nr_5F2298 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37606 (s : N.State) (i : N.Inputs) :
  R.v37606 (state s) (inputs i) = Zmod.unsigned (N.v37606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37606 s i)) at 1.
  unfold R.v37606, N.v37606.
  unfold R.v6, N.v6.
  rewrite ?node_16115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37607 (s : N.State) (i : N.Inputs) :
  R.v37607 (state s) (inputs i) = Zmod.unsigned (N.v37607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37607 s i)) at 1.
  unfold R.v37607, N.v37607.
  rewrite ?node_37605.
  rewrite ?node_37606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37608 (s : N.State) (i : N.Inputs) :
  R.v37608 (state s) (inputs i) = Zmod.unsigned (N.v37608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37608 s i)) at 1.
  unfold R.v37608, N.v37608.
  unfold R.v16484, N.v16484.
  rewrite ?node_37607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37609 (s : N.State) (i : N.Inputs) :
  R.v37609 (state s) (inputs i) = Zmod.unsigned (N.v37609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37609 s i)) at 1.
  unfold R.v37609, N.v37609.
  rewrite ?node_37604.
  rewrite ?node_37608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37610 (s : N.State) (i : N.Inputs) :
  R.v37610 (state s) (inputs i) = Zmod.unsigned (N.v37610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37610 s i)) at 1.
  unfold R.v37610, N.v37610.
  unfold R.v6, N.v6.
  rewrite ?node_37609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37611 (s : N.State) (i : N.Inputs) :
  R.v37611 (state s) (inputs i) = Zmod.unsigned (N.v37611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37611 s i)) at 1.
  unfold R.v37611, N.v37611.
  rewrite ?node_16120.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37612 (s : N.State) (i : N.Inputs) :
  R.v37612 (state s) (inputs i) = Zmod.unsigned (N.v37612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37612 s i)) at 1.
  unfold R.v37612, N.v37612.
  unfold R.v6, N.v6.
  rewrite ?node_16141.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37613 (s : N.State) (i : N.Inputs) :
  R.v37613 (state s) (inputs i) = Zmod.unsigned (N.v37613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37613 s i)) at 1.
  unfold R.v37613, N.v37613.
  rewrite ?node_37611.
  rewrite ?node_37612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37614 (s : N.State) (i : N.Inputs) :
  R.v37614 (state s) (inputs i) = Zmod.unsigned (N.v37614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37614 s i)) at 1.
  unfold R.v37614, N.v37614.
  rewrite ?node_37610.
  rewrite ?node_37613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37615 (s : N.State) (i : N.Inputs) :
  R.v37615 (state s) (inputs i) = Zmod.unsigned (N.v37615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37615 s i)) at 1.
  unfold R.v37615, N.v37615.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37616 (s : N.State) (i : N.Inputs) :
  R.v37616 (state s) (inputs i) = Zmod.unsigned (N.v37616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37616 s i)) at 1.
  unfold R.v37616, N.v37616.
  unfold R.v16463, N.v16463.
  rewrite !state_r2272_nr_5F2301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2272_nr_5F2301 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37617 (s : N.State) (i : N.Inputs) :
  R.v37617 (state s) (inputs i) = Zmod.unsigned (N.v37617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37617 s i)) at 1.
  unfold R.v37617, N.v37617.
  unfold R.v6, N.v6.
  rewrite !state_r2271_nr_5F2300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2271_nr_5F2300 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37618 (s : N.State) (i : N.Inputs) :
  R.v37618 (state s) (inputs i) = Zmod.unsigned (N.v37618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37618 s i)) at 1.
  unfold R.v37618, N.v37618.
  unfold R.v6, N.v6.
  rewrite !state_r2270_nr_5F2299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2270_nr_5F2299 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37619 (s : N.State) (i : N.Inputs) :
  R.v37619 (state s) (inputs i) = Zmod.unsigned (N.v37619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37619 s i)) at 1.
  unfold R.v37619, N.v37619.
  rewrite ?node_37617.
  rewrite ?node_37618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37620 (s : N.State) (i : N.Inputs) :
  R.v37620 (state s) (inputs i) = Zmod.unsigned (N.v37620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37620 s i)) at 1.
  unfold R.v37620, N.v37620.
  unfold R.v16484, N.v16484.
  rewrite ?node_37619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37621 (s : N.State) (i : N.Inputs) :
  R.v37621 (state s) (inputs i) = Zmod.unsigned (N.v37621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37621 s i)) at 1.
  unfold R.v37621, N.v37621.
  rewrite ?node_37616.
  rewrite ?node_37620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37622 (s : N.State) (i : N.Inputs) :
  R.v37622 (state s) (inputs i) = Zmod.unsigned (N.v37622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37622 s i)) at 1.
  unfold R.v37622, N.v37622.
  unfold R.v6, N.v6.
  rewrite ?node_37621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37623 (s : N.State) (i : N.Inputs) :
  R.v37623 (state s) (inputs i) = Zmod.unsigned (N.v37623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37623 s i)) at 1.
  unfold R.v37623, N.v37623.
  rewrite ?node_16135.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37624 (s : N.State) (i : N.Inputs) :
  R.v37624 (state s) (inputs i) = Zmod.unsigned (N.v37624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37624 s i)) at 1.
  unfold R.v37624, N.v37624.
  unfold R.v6, N.v6.
  rewrite ?node_16156.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37625 (s : N.State) (i : N.Inputs) :
  R.v37625 (state s) (inputs i) = Zmod.unsigned (N.v37625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37625 s i)) at 1.
  unfold R.v37625, N.v37625.
  rewrite ?node_37623.
  rewrite ?node_37624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37626 (s : N.State) (i : N.Inputs) :
  R.v37626 (state s) (inputs i) = Zmod.unsigned (N.v37626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37626 s i)) at 1.
  unfold R.v37626, N.v37626.
  rewrite ?node_37622.
  rewrite ?node_37625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37627 (s : N.State) (i : N.Inputs) :
  R.v37627 (state s) (inputs i) = Zmod.unsigned (N.v37627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37627 s i)) at 1.
  unfold R.v37627, N.v37627.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37628 (s : N.State) (i : N.Inputs) :
  R.v37628 (state s) (inputs i) = Zmod.unsigned (N.v37628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37628 s i)) at 1.
  unfold R.v37628, N.v37628.
  unfold R.v16463, N.v16463.
  rewrite !state_r2274_nr_5F2304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2274_nr_5F2304 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37629 (s : N.State) (i : N.Inputs) :
  R.v37629 (state s) (inputs i) = Zmod.unsigned (N.v37629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37629 s i)) at 1.
  unfold R.v37629, N.v37629.
  unfold R.v6, N.v6.
  rewrite !state_r2273_nr_5F2303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2273_nr_5F2303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37630 (s : N.State) (i : N.Inputs) :
  R.v37630 (state s) (inputs i) = Zmod.unsigned (N.v37630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37630 s i)) at 1.
  unfold R.v37630, N.v37630.
  unfold R.v19, N.v19.
  rewrite ?node_37629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37631 (s : N.State) (i : N.Inputs) :
  R.v37631 (state s) (inputs i) = Zmod.unsigned (N.v37631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37631 s i)) at 1.
  unfold R.v37631, N.v37631.
  unfold R.v16484, N.v16484.
  rewrite ?node_37630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37632 (s : N.State) (i : N.Inputs) :
  R.v37632 (state s) (inputs i) = Zmod.unsigned (N.v37632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37632 s i)) at 1.
  unfold R.v37632, N.v37632.
  rewrite ?node_37628.
  rewrite ?node_37631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37633 (s : N.State) (i : N.Inputs) :
  R.v37633 (state s) (inputs i) = Zmod.unsigned (N.v37633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37633 s i)) at 1.
  unfold R.v37633, N.v37633.
  unfold R.v6, N.v6.
  rewrite ?node_37632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37634 (s : N.State) (i : N.Inputs) :
  R.v37634 (state s) (inputs i) = Zmod.unsigned (N.v37634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37634 s i)) at 1.
  unfold R.v37634, N.v37634.
  rewrite ?node_16153.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37635 (s : N.State) (i : N.Inputs) :
  R.v37635 (state s) (inputs i) = Zmod.unsigned (N.v37635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37635 s i)) at 1.
  unfold R.v37635, N.v37635.
  unfold R.v6, N.v6.
  rewrite ?node_16171.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37636 (s : N.State) (i : N.Inputs) :
  R.v37636 (state s) (inputs i) = Zmod.unsigned (N.v37636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37636 s i)) at 1.
  unfold R.v37636, N.v37636.
  rewrite ?node_37634.
  rewrite ?node_37635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37637 (s : N.State) (i : N.Inputs) :
  R.v37637 (state s) (inputs i) = Zmod.unsigned (N.v37637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37637 s i)) at 1.
  unfold R.v37637, N.v37637.
  rewrite ?node_37633.
  rewrite ?node_37636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37638 (s : N.State) (i : N.Inputs) :
  R.v37638 (state s) (inputs i) = Zmod.unsigned (N.v37638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37638 s i)) at 1.
  unfold R.v37638, N.v37638.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37639 (s : N.State) (i : N.Inputs) :
  R.v37639 (state s) (inputs i) = Zmod.unsigned (N.v37639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37639 s i)) at 1.
  unfold R.v37639, N.v37639.
  unfold R.v6, N.v6.
  rewrite !state_r2276_nr_5F2306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2276_nr_5F2306 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37640 (s : N.State) (i : N.Inputs) :
  R.v37640 (state s) (inputs i) = Zmod.unsigned (N.v37640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37640 s i)) at 1.
  unfold R.v37640, N.v37640.
  unfold R.v6, N.v6.
  rewrite !state_r2275_nr_5F2305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2275_nr_5F2305 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37641 (s : N.State) (i : N.Inputs) :
  R.v37641 (state s) (inputs i) = Zmod.unsigned (N.v37641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37641 s i)) at 1.
  unfold R.v37641, N.v37641.
  rewrite ?node_37639.
  rewrite ?node_37640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37642 (s : N.State) (i : N.Inputs) :
  R.v37642 (state s) (inputs i) = Zmod.unsigned (N.v37642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37642 s i)) at 1.
  unfold R.v37642, N.v37642.
  unfold R.v16463, N.v16463.
  rewrite ?node_37641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37643 (s : N.State) (i : N.Inputs) :
  R.v37643 (state s) (inputs i) = Zmod.unsigned (N.v37643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37643 s i)) at 1.
  unfold R.v37643, N.v37643.
  rewrite ?node_16169.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37644 (s : N.State) (i : N.Inputs) :
  R.v37644 (state s) (inputs i) = Zmod.unsigned (N.v37644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37644 s i)) at 1.
  unfold R.v37644, N.v37644.
  unfold R.v6, N.v6.
  rewrite ?node_16183.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37645 (s : N.State) (i : N.Inputs) :
  R.v37645 (state s) (inputs i) = Zmod.unsigned (N.v37645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37645 s i)) at 1.
  unfold R.v37645, N.v37645.
  rewrite ?node_37643.
  rewrite ?node_37644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37646 (s : N.State) (i : N.Inputs) :
  R.v37646 (state s) (inputs i) = Zmod.unsigned (N.v37646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37646 s i)) at 1.
  unfold R.v37646, N.v37646.
  rewrite ?node_37642.
  rewrite ?node_37645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37647 (s : N.State) (i : N.Inputs) :
  R.v37647 (state s) (inputs i) = Zmod.unsigned (N.v37647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37647 s i)) at 1.
  unfold R.v37647, N.v37647.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37648 (s : N.State) (i : N.Inputs) :
  R.v37648 (state s) (inputs i) = Zmod.unsigned (N.v37648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37648 s i)) at 1.
  unfold R.v37648, N.v37648.
  unfold R.v6, N.v6.
  rewrite !state_r2277_nr_5F2308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2277_nr_5F2308 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37649 (s : N.State) (i : N.Inputs) :
  R.v37649 (state s) (inputs i) = Zmod.unsigned (N.v37649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37649 s i)) at 1.
  unfold R.v37649, N.v37649.
  unfold R.v19, N.v19.
  rewrite ?node_37648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37650 (s : N.State) (i : N.Inputs) :
  R.v37650 (state s) (inputs i) = Zmod.unsigned (N.v37650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37650 s i)) at 1.
  unfold R.v37650, N.v37650.
  unfold R.v16463, N.v16463.
  rewrite ?node_37649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37651 (s : N.State) (i : N.Inputs) :
  R.v37651 (state s) (inputs i) = Zmod.unsigned (N.v37651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37651 s i)) at 1.
  unfold R.v37651, N.v37651.
  rewrite ?node_16182.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37652 (s : N.State) (i : N.Inputs) :
  R.v37652 (state s) (inputs i) = Zmod.unsigned (N.v37652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37652 s i)) at 1.
  unfold R.v37652, N.v37652.
  unfold R.v6, N.v6.
  unfold R.v16463, N.v16463.
  rewrite !state_r2277_nr_5F2308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2277_nr_5F2308 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37653 (s : N.State) (i : N.Inputs) :
  R.v37653 (state s) (inputs i) = Zmod.unsigned (N.v37653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37653 s i)) at 1.
  unfold R.v37653, N.v37653.
  rewrite ?node_37651.
  rewrite ?node_37652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37654 (s : N.State) (i : N.Inputs) :
  R.v37654 (state s) (inputs i) = Zmod.unsigned (N.v37654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37654 s i)) at 1.
  unfold R.v37654, N.v37654.
  rewrite ?node_37650.
  rewrite ?node_37653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37655 (s : N.State) (i : N.Inputs) :
  R.v37655 (state s) (inputs i) = Zmod.unsigned (N.v37655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37655 s i)) at 1.
  unfold R.v37655, N.v37655.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37656 (s : N.State) (i : N.Inputs) :
  R.v37656 (state s) (inputs i) = Zmod.unsigned (N.v37656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37656 s i)) at 1.
  unfold R.v37656, N.v37656.
  unfold R.v6, N.v6.
  rewrite ?node_5104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37657 (s : N.State) (i : N.Inputs) :
  R.v37657 (state s) (inputs i) = Zmod.unsigned (N.v37657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37657 s i)) at 1.
  unfold R.v37657, N.v37657.
  unfold R.v6, N.v6.
  rewrite ?node_5103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37658 (s : N.State) (i : N.Inputs) :
  R.v37658 (state s) (inputs i) = Zmod.unsigned (N.v37658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37658 s i)) at 1.
  unfold R.v37658, N.v37658.
  rewrite ?node_37656.
  rewrite ?node_37657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37659 (s : N.State) (i : N.Inputs) :
  R.v37659 (state s) (inputs i) = Zmod.unsigned (N.v37659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37659 s i)) at 1.
  unfold R.v37659, N.v37659.
  unfold R.v16463, N.v16463.
  rewrite ?node_37658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37660 (s : N.State) (i : N.Inputs) :
  R.v37660 (state s) (inputs i) = Zmod.unsigned (N.v37660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37660 s i)) at 1.
  unfold R.v37660, N.v37660.
  rewrite ?node_5105.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37661 (s : N.State) (i : N.Inputs) :
  R.v37661 (state s) (inputs i) = Zmod.unsigned (N.v37661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37661 s i)) at 1.
  unfold R.v37661, N.v37661.
  unfold R.v6, N.v6.
  rewrite ?node_5111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37662 (s : N.State) (i : N.Inputs) :
  R.v37662 (state s) (inputs i) = Zmod.unsigned (N.v37662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37662 s i)) at 1.
  unfold R.v37662, N.v37662.
  rewrite ?node_37660.
  rewrite ?node_37661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37663 (s : N.State) (i : N.Inputs) :
  R.v37663 (state s) (inputs i) = Zmod.unsigned (N.v37663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37663 s i)) at 1.
  unfold R.v37663, N.v37663.
  rewrite ?node_37659.
  rewrite ?node_37662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37664 (s : N.State) (i : N.Inputs) :
  R.v37664 (state s) (inputs i) = Zmod.unsigned (N.v37664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37664 s i)) at 1.
  unfold R.v37664, N.v37664.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37665 (s : N.State) (i : N.Inputs) :
  R.v37665 (state s) (inputs i) = Zmod.unsigned (N.v37665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37665 s i)) at 1.
  unfold R.v37665, N.v37665.
  unfold R.v6, N.v6.
  rewrite ?node_5109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37666 (s : N.State) (i : N.Inputs) :
  R.v37666 (state s) (inputs i) = Zmod.unsigned (N.v37666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37666 s i)) at 1.
  unfold R.v37666, N.v37666.
  unfold R.v6, N.v6.
  rewrite ?node_5108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37667 (s : N.State) (i : N.Inputs) :
  R.v37667 (state s) (inputs i) = Zmod.unsigned (N.v37667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37667 s i)) at 1.
  unfold R.v37667, N.v37667.
  rewrite ?node_37665.
  rewrite ?node_37666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37668 (s : N.State) (i : N.Inputs) :
  R.v37668 (state s) (inputs i) = Zmod.unsigned (N.v37668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37668 s i)) at 1.
  unfold R.v37668, N.v37668.
  unfold R.v16463, N.v16463.
  rewrite ?node_37667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37669 (s : N.State) (i : N.Inputs) :
  R.v37669 (state s) (inputs i) = Zmod.unsigned (N.v37669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37669 s i)) at 1.
  unfold R.v37669, N.v37669.
  rewrite ?node_5110.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37670 (s : N.State) (i : N.Inputs) :
  R.v37670 (state s) (inputs i) = Zmod.unsigned (N.v37670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37670 s i)) at 1.
  unfold R.v37670, N.v37670.
  unfold R.v6, N.v6.
  rewrite ?node_5120.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37671 (s : N.State) (i : N.Inputs) :
  R.v37671 (state s) (inputs i) = Zmod.unsigned (N.v37671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37671 s i)) at 1.
  unfold R.v37671, N.v37671.
  rewrite ?node_37669.
  rewrite ?node_37670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37672 (s : N.State) (i : N.Inputs) :
  R.v37672 (state s) (inputs i) = Zmod.unsigned (N.v37672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37672 s i)) at 1.
  unfold R.v37672, N.v37672.
  rewrite ?node_37668.
  rewrite ?node_37671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37673 (s : N.State) (i : N.Inputs) :
  R.v37673 (state s) (inputs i) = Zmod.unsigned (N.v37673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37673 s i)) at 1.
  unfold R.v37673, N.v37673.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37674 (s : N.State) (i : N.Inputs) :
  R.v37674 (state s) (inputs i) = Zmod.unsigned (N.v37674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37674 s i)) at 1.
  unfold R.v37674, N.v37674.
  unfold R.v6, N.v6.
  rewrite ?node_5118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37675 (s : N.State) (i : N.Inputs) :
  R.v37675 (state s) (inputs i) = Zmod.unsigned (N.v37675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37675 s i)) at 1.
  unfold R.v37675, N.v37675.
  unfold R.v6, N.v6.
  rewrite ?node_5115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37676 (s : N.State) (i : N.Inputs) :
  R.v37676 (state s) (inputs i) = Zmod.unsigned (N.v37676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37676 s i)) at 1.
  unfold R.v37676, N.v37676.
  rewrite ?node_37674.
  rewrite ?node_37675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37677 (s : N.State) (i : N.Inputs) :
  R.v37677 (state s) (inputs i) = Zmod.unsigned (N.v37677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37677 s i)) at 1.
  unfold R.v37677, N.v37677.
  unfold R.v16463, N.v16463.
  rewrite ?node_37676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37678 (s : N.State) (i : N.Inputs) :
  R.v37678 (state s) (inputs i) = Zmod.unsigned (N.v37678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37678 s i)) at 1.
  unfold R.v37678, N.v37678.
  rewrite ?node_5119.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37679 (s : N.State) (i : N.Inputs) :
  R.v37679 (state s) (inputs i) = Zmod.unsigned (N.v37679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37679 s i)) at 1.
  unfold R.v37679, N.v37679.
  unfold R.v6, N.v6.
  rewrite ?node_5132.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37680 (s : N.State) (i : N.Inputs) :
  R.v37680 (state s) (inputs i) = Zmod.unsigned (N.v37680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37680 s i)) at 1.
  unfold R.v37680, N.v37680.
  rewrite ?node_37678.
  rewrite ?node_37679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37681 (s : N.State) (i : N.Inputs) :
  R.v37681 (state s) (inputs i) = Zmod.unsigned (N.v37681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37681 s i)) at 1.
  unfold R.v37681, N.v37681.
  rewrite ?node_37677.
  rewrite ?node_37680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37682 (s : N.State) (i : N.Inputs) :
  R.v37682 (state s) (inputs i) = Zmod.unsigned (N.v37682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37682 s i)) at 1.
  unfold R.v37682, N.v37682.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37683 (s : N.State) (i : N.Inputs) :
  R.v37683 (state s) (inputs i) = Zmod.unsigned (N.v37683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37683 s i)) at 1.
  unfold R.v37683, N.v37683.
  unfold R.v6, N.v6.
  rewrite ?node_5130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37684 (s : N.State) (i : N.Inputs) :
  R.v37684 (state s) (inputs i) = Zmod.unsigned (N.v37684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37684 s i)) at 1.
  unfold R.v37684, N.v37684.
  unfold R.v6, N.v6.
  rewrite ?node_5127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37685 (s : N.State) (i : N.Inputs) :
  R.v37685 (state s) (inputs i) = Zmod.unsigned (N.v37685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37685 s i)) at 1.
  unfold R.v37685, N.v37685.
  rewrite ?node_37683.
  rewrite ?node_37684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37686 (s : N.State) (i : N.Inputs) :
  R.v37686 (state s) (inputs i) = Zmod.unsigned (N.v37686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37686 s i)) at 1.
  unfold R.v37686, N.v37686.
  unfold R.v16463, N.v16463.
  rewrite ?node_37685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37687 (s : N.State) (i : N.Inputs) :
  R.v37687 (state s) (inputs i) = Zmod.unsigned (N.v37687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37687 s i)) at 1.
  unfold R.v37687, N.v37687.
  rewrite ?node_5131.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37688 (s : N.State) (i : N.Inputs) :
  R.v37688 (state s) (inputs i) = Zmod.unsigned (N.v37688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37688 s i)) at 1.
  unfold R.v37688, N.v37688.
  unfold R.v6, N.v6.
  rewrite ?node_5148.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37689 (s : N.State) (i : N.Inputs) :
  R.v37689 (state s) (inputs i) = Zmod.unsigned (N.v37689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37689 s i)) at 1.
  unfold R.v37689, N.v37689.
  rewrite ?node_37687.
  rewrite ?node_37688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37690 (s : N.State) (i : N.Inputs) :
  R.v37690 (state s) (inputs i) = Zmod.unsigned (N.v37690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37690 s i)) at 1.
  unfold R.v37690, N.v37690.
  rewrite ?node_37686.
  rewrite ?node_37689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37691 (s : N.State) (i : N.Inputs) :
  R.v37691 (state s) (inputs i) = Zmod.unsigned (N.v37691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37691 s i)) at 1.
  unfold R.v37691, N.v37691.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37692 (s : N.State) (i : N.Inputs) :
  R.v37692 (state s) (inputs i) = Zmod.unsigned (N.v37692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37692 s i)) at 1.
  unfold R.v37692, N.v37692.
  unfold R.v6, N.v6.
  rewrite ?node_5146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37693 (s : N.State) (i : N.Inputs) :
  R.v37693 (state s) (inputs i) = Zmod.unsigned (N.v37693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37693 s i)) at 1.
  unfold R.v37693, N.v37693.
  unfold R.v6, N.v6.
  rewrite ?node_5145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37694 (s : N.State) (i : N.Inputs) :
  R.v37694 (state s) (inputs i) = Zmod.unsigned (N.v37694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37694 s i)) at 1.
  unfold R.v37694, N.v37694.
  rewrite ?node_37692.
  rewrite ?node_37693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37695 (s : N.State) (i : N.Inputs) :
  R.v37695 (state s) (inputs i) = Zmod.unsigned (N.v37695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37695 s i)) at 1.
  unfold R.v37695, N.v37695.
  unfold R.v16463, N.v16463.
  rewrite ?node_37694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37696 (s : N.State) (i : N.Inputs) :
  R.v37696 (state s) (inputs i) = Zmod.unsigned (N.v37696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37696 s i)) at 1.
  unfold R.v37696, N.v37696.
  rewrite ?node_5147.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37697 (s : N.State) (i : N.Inputs) :
  R.v37697 (state s) (inputs i) = Zmod.unsigned (N.v37697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37697 s i)) at 1.
  unfold R.v37697, N.v37697.
  unfold R.v6, N.v6.
  rewrite ?node_5169.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37698 (s : N.State) (i : N.Inputs) :
  R.v37698 (state s) (inputs i) = Zmod.unsigned (N.v37698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37698 s i)) at 1.
  unfold R.v37698, N.v37698.
  rewrite ?node_37696.
  rewrite ?node_37697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37699 (s : N.State) (i : N.Inputs) :
  R.v37699 (state s) (inputs i) = Zmod.unsigned (N.v37699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37699 s i)) at 1.
  unfold R.v37699, N.v37699.
  rewrite ?node_37695.
  rewrite ?node_37698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37700 (s : N.State) (i : N.Inputs) :
  R.v37700 (state s) (inputs i) = Zmod.unsigned (N.v37700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37700 s i)) at 1.
  unfold R.v37700, N.v37700.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37701 (s : N.State) (i : N.Inputs) :
  R.v37701 (state s) (inputs i) = Zmod.unsigned (N.v37701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37701 s i)) at 1.
  unfold R.v37701, N.v37701.
  rewrite ?node_5167.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37702 (s : N.State) (i : N.Inputs) :
  R.v37702 (state s) (inputs i) = Zmod.unsigned (N.v37702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37702 s i)) at 1.
  unfold R.v37702, N.v37702.
  unfold R.v6, N.v6.
  rewrite !state_r22_nr_5F22.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r22_nr_5F22 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37703 (s : N.State) (i : N.Inputs) :
  R.v37703 (state s) (inputs i) = Zmod.unsigned (N.v37703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37703 s i)) at 1.
  unfold R.v37703, N.v37703.
  unfold R.v6, N.v6.
  rewrite ?node_5163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37704 (s : N.State) (i : N.Inputs) :
  R.v37704 (state s) (inputs i) = Zmod.unsigned (N.v37704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37704 s i)) at 1.
  unfold R.v37704, N.v37704.
  rewrite ?node_37702.
  rewrite ?node_37703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37705 (s : N.State) (i : N.Inputs) :
  R.v37705 (state s) (inputs i) = Zmod.unsigned (N.v37705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37705 s i)) at 1.
  unfold R.v37705, N.v37705.
  unfold R.v16484, N.v16484.
  rewrite ?node_37704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37706 (s : N.State) (i : N.Inputs) :
  R.v37706 (state s) (inputs i) = Zmod.unsigned (N.v37706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37706 s i)) at 1.
  unfold R.v37706, N.v37706.
  rewrite ?node_37701.
  rewrite ?node_37705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37707 (s : N.State) (i : N.Inputs) :
  R.v37707 (state s) (inputs i) = Zmod.unsigned (N.v37707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37707 s i)) at 1.
  unfold R.v37707, N.v37707.
  unfold R.v6, N.v6.
  rewrite ?node_37706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37708 (s : N.State) (i : N.Inputs) :
  R.v37708 (state s) (inputs i) = Zmod.unsigned (N.v37708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37708 s i)) at 1.
  unfold R.v37708, N.v37708.
  rewrite ?node_5168.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37709 (s : N.State) (i : N.Inputs) :
  R.v37709 (state s) (inputs i) = Zmod.unsigned (N.v37709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37709 s i)) at 1.
  unfold R.v37709, N.v37709.
  unfold R.v6, N.v6.
  rewrite ?node_5192.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37710 (s : N.State) (i : N.Inputs) :
  R.v37710 (state s) (inputs i) = Zmod.unsigned (N.v37710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37710 s i)) at 1.
  unfold R.v37710, N.v37710.
  rewrite ?node_37708.
  rewrite ?node_37709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37711 (s : N.State) (i : N.Inputs) :
  R.v37711 (state s) (inputs i) = Zmod.unsigned (N.v37711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37711 s i)) at 1.
  unfold R.v37711, N.v37711.
  rewrite ?node_37707.
  rewrite ?node_37710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37712 (s : N.State) (i : N.Inputs) :
  R.v37712 (state s) (inputs i) = Zmod.unsigned (N.v37712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37712 s i)) at 1.
  unfold R.v37712, N.v37712.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37713 (s : N.State) (i : N.Inputs) :
  R.v37713 (state s) (inputs i) = Zmod.unsigned (N.v37713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37713 s i)) at 1.
  unfold R.v37713, N.v37713.
  rewrite ?node_5188.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37714 (s : N.State) (i : N.Inputs) :
  R.v37714 (state s) (inputs i) = Zmod.unsigned (N.v37714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37714 s i)) at 1.
  unfold R.v37714, N.v37714.
  unfold R.v6, N.v6.
  rewrite !state_r27_nr_5F27.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r27_nr_5F27 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37715 (s : N.State) (i : N.Inputs) :
  R.v37715 (state s) (inputs i) = Zmod.unsigned (N.v37715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37715 s i)) at 1.
  unfold R.v37715, N.v37715.
  unfold R.v6, N.v6.
  rewrite ?node_5184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37716 (s : N.State) (i : N.Inputs) :
  R.v37716 (state s) (inputs i) = Zmod.unsigned (N.v37716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37716 s i)) at 1.
  unfold R.v37716, N.v37716.
  rewrite ?node_37714.
  rewrite ?node_37715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37717 (s : N.State) (i : N.Inputs) :
  R.v37717 (state s) (inputs i) = Zmod.unsigned (N.v37717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37717 s i)) at 1.
  unfold R.v37717, N.v37717.
  unfold R.v16484, N.v16484.
  rewrite ?node_37716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37718 (s : N.State) (i : N.Inputs) :
  R.v37718 (state s) (inputs i) = Zmod.unsigned (N.v37718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37718 s i)) at 1.
  unfold R.v37718, N.v37718.
  rewrite ?node_37713.
  rewrite ?node_37717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37719 (s : N.State) (i : N.Inputs) :
  R.v37719 (state s) (inputs i) = Zmod.unsigned (N.v37719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37719 s i)) at 1.
  unfold R.v37719, N.v37719.
  unfold R.v6, N.v6.
  rewrite ?node_37718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37720 (s : N.State) (i : N.Inputs) :
  R.v37720 (state s) (inputs i) = Zmod.unsigned (N.v37720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37720 s i)) at 1.
  unfold R.v37720, N.v37720.
  rewrite ?node_5189.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37721 (s : N.State) (i : N.Inputs) :
  R.v37721 (state s) (inputs i) = Zmod.unsigned (N.v37721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37721 s i)) at 1.
  unfold R.v37721, N.v37721.
  unfold R.v6, N.v6.
  rewrite ?node_5216.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37722 (s : N.State) (i : N.Inputs) :
  R.v37722 (state s) (inputs i) = Zmod.unsigned (N.v37722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37722 s i)) at 1.
  unfold R.v37722, N.v37722.
  rewrite ?node_37720.
  rewrite ?node_37721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37723 (s : N.State) (i : N.Inputs) :
  R.v37723 (state s) (inputs i) = Zmod.unsigned (N.v37723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37723 s i)) at 1.
  unfold R.v37723, N.v37723.
  rewrite ?node_37719.
  rewrite ?node_37722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37724 (s : N.State) (i : N.Inputs) :
  R.v37724 (state s) (inputs i) = Zmod.unsigned (N.v37724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37724 s i)) at 1.
  unfold R.v37724, N.v37724.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37725 (s : N.State) (i : N.Inputs) :
  R.v37725 (state s) (inputs i) = Zmod.unsigned (N.v37725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37725 s i)) at 1.
  unfold R.v37725, N.v37725.
  rewrite ?node_5212.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37726 (s : N.State) (i : N.Inputs) :
  R.v37726 (state s) (inputs i) = Zmod.unsigned (N.v37726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37726 s i)) at 1.
  unfold R.v37726, N.v37726.
  unfold R.v6, N.v6.
  rewrite ?node_5208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37727 (s : N.State) (i : N.Inputs) :
  R.v37727 (state s) (inputs i) = Zmod.unsigned (N.v37727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37727 s i)) at 1.
  unfold R.v37727, N.v37727.
  unfold R.v6, N.v6.
  rewrite ?node_5207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37728 (s : N.State) (i : N.Inputs) :
  R.v37728 (state s) (inputs i) = Zmod.unsigned (N.v37728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37728 s i)) at 1.
  unfold R.v37728, N.v37728.
  rewrite ?node_37726.
  rewrite ?node_37727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37729 (s : N.State) (i : N.Inputs) :
  R.v37729 (state s) (inputs i) = Zmod.unsigned (N.v37729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37729 s i)) at 1.
  unfold R.v37729, N.v37729.
  unfold R.v16484, N.v16484.
  rewrite ?node_37728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37730 (s : N.State) (i : N.Inputs) :
  R.v37730 (state s) (inputs i) = Zmod.unsigned (N.v37730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37730 s i)) at 1.
  unfold R.v37730, N.v37730.
  rewrite ?node_37725.
  rewrite ?node_37729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37731 (s : N.State) (i : N.Inputs) :
  R.v37731 (state s) (inputs i) = Zmod.unsigned (N.v37731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37731 s i)) at 1.
  unfold R.v37731, N.v37731.
  unfold R.v6, N.v6.
  rewrite ?node_37730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37732 (s : N.State) (i : N.Inputs) :
  R.v37732 (state s) (inputs i) = Zmod.unsigned (N.v37732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37732 s i)) at 1.
  unfold R.v37732, N.v37732.
  rewrite ?node_5213.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37733 (s : N.State) (i : N.Inputs) :
  R.v37733 (state s) (inputs i) = Zmod.unsigned (N.v37733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37733 s i)) at 1.
  unfold R.v37733, N.v37733.
  unfold R.v6, N.v6.
  rewrite ?node_5242.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37734 (s : N.State) (i : N.Inputs) :
  R.v37734 (state s) (inputs i) = Zmod.unsigned (N.v37734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37734 s i)) at 1.
  unfold R.v37734, N.v37734.
  rewrite ?node_37732.
  rewrite ?node_37733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37735 (s : N.State) (i : N.Inputs) :
  R.v37735 (state s) (inputs i) = Zmod.unsigned (N.v37735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37735 s i)) at 1.
  unfold R.v37735, N.v37735.
  rewrite ?node_37731.
  rewrite ?node_37734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37736 (s : N.State) (i : N.Inputs) :
  R.v37736 (state s) (inputs i) = Zmod.unsigned (N.v37736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37736 s i)) at 1.
  unfold R.v37736, N.v37736.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37737 (s : N.State) (i : N.Inputs) :
  R.v37737 (state s) (inputs i) = Zmod.unsigned (N.v37737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37737 s i)) at 1.
  unfold R.v37737, N.v37737.
  rewrite ?node_5238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37738 (s : N.State) (i : N.Inputs) :
  R.v37738 (state s) (inputs i) = Zmod.unsigned (N.v37738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37738 s i)) at 1.
  unfold R.v37738, N.v37738.
  rewrite ?node_5236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37739 (s : N.State) (i : N.Inputs) :
  R.v37739 (state s) (inputs i) = Zmod.unsigned (N.v37739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37739 s i)) at 1.
  unfold R.v37739, N.v37739.
  unfold R.v6, N.v6.
  rewrite ?node_5232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37740 (s : N.State) (i : N.Inputs) :
  R.v37740 (state s) (inputs i) = Zmod.unsigned (N.v37740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37740 s i)) at 1.
  unfold R.v37740, N.v37740.
  unfold R.v6, N.v6.
  rewrite ?node_5231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37741 (s : N.State) (i : N.Inputs) :
  R.v37741 (state s) (inputs i) = Zmod.unsigned (N.v37741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37741 s i)) at 1.
  unfold R.v37741, N.v37741.
  rewrite ?node_37739.
  rewrite ?node_37740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37742 (s : N.State) (i : N.Inputs) :
  R.v37742 (state s) (inputs i) = Zmod.unsigned (N.v37742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37742 s i)) at 1.
  unfold R.v37742, N.v37742.
  unfold R.v16484, N.v16484.
  rewrite ?node_37741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37743 (s : N.State) (i : N.Inputs) :
  R.v37743 (state s) (inputs i) = Zmod.unsigned (N.v37743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37743 s i)) at 1.
  unfold R.v37743, N.v37743.
  rewrite ?node_37737.
  rewrite ?node_37738.
  rewrite ?node_37742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37744 (s : N.State) (i : N.Inputs) :
  R.v37744 (state s) (inputs i) = Zmod.unsigned (N.v37744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37744 s i)) at 1.
  unfold R.v37744, N.v37744.
  unfold R.v6, N.v6.
  rewrite ?node_37743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37745 (s : N.State) (i : N.Inputs) :
  R.v37745 (state s) (inputs i) = Zmod.unsigned (N.v37745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37745 s i)) at 1.
  unfold R.v37745, N.v37745.
  rewrite ?node_5239.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37746 (s : N.State) (i : N.Inputs) :
  R.v37746 (state s) (inputs i) = Zmod.unsigned (N.v37746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37746 s i)) at 1.
  unfold R.v37746, N.v37746.
  unfold R.v6, N.v6.
  rewrite ?node_5269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37747 (s : N.State) (i : N.Inputs) :
  R.v37747 (state s) (inputs i) = Zmod.unsigned (N.v37747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37747 s i)) at 1.
  unfold R.v37747, N.v37747.
  unfold R.v6, N.v6.
  rewrite ?node_5271.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37748 (s : N.State) (i : N.Inputs) :
  R.v37748 (state s) (inputs i) = Zmod.unsigned (N.v37748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37748 s i)) at 1.
  unfold R.v37748, N.v37748.
  rewrite ?node_37745.
  rewrite ?node_37746.
  rewrite ?node_37747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37749 (s : N.State) (i : N.Inputs) :
  R.v37749 (state s) (inputs i) = Zmod.unsigned (N.v37749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37749 s i)) at 1.
  unfold R.v37749, N.v37749.
  rewrite ?node_37744.
  rewrite ?node_37748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37750 (s : N.State) (i : N.Inputs) :
  R.v37750 (state s) (inputs i) = Zmod.unsigned (N.v37750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37750 s i)) at 1.
  unfold R.v37750, N.v37750.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37751 (s : N.State) (i : N.Inputs) :
  R.v37751 (state s) (inputs i) = Zmod.unsigned (N.v37751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37751 s i)) at 1.
  unfold R.v37751, N.v37751.
  rewrite ?node_5236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37752 (s : N.State) (i : N.Inputs) :
  R.v37752 (state s) (inputs i) = Zmod.unsigned (N.v37752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37752 s i)) at 1.
  unfold R.v37752, N.v37752.
  unfold R.v6, N.v6.
  rewrite ?node_5232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37753 (s : N.State) (i : N.Inputs) :
  R.v37753 (state s) (inputs i) = Zmod.unsigned (N.v37753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37753 s i)) at 1.
  unfold R.v37753, N.v37753.
  unfold R.v6, N.v6.
  rewrite ?node_5231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37754 (s : N.State) (i : N.Inputs) :
  R.v37754 (state s) (inputs i) = Zmod.unsigned (N.v37754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37754 s i)) at 1.
  unfold R.v37754, N.v37754.
  rewrite ?node_37752.
  rewrite ?node_37753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37755 (s : N.State) (i : N.Inputs) :
  R.v37755 (state s) (inputs i) = Zmod.unsigned (N.v37755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37755 s i)) at 1.
  unfold R.v37755, N.v37755.
  unfold R.v16484, N.v16484.
  rewrite ?node_37754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37756 (s : N.State) (i : N.Inputs) :
  R.v37756 (state s) (inputs i) = Zmod.unsigned (N.v37756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37756 s i)) at 1.
  unfold R.v37756, N.v37756.
  rewrite ?node_37751.
  rewrite ?node_37755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37757 (s : N.State) (i : N.Inputs) :
  R.v37757 (state s) (inputs i) = Zmod.unsigned (N.v37757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37757 s i)) at 1.
  unfold R.v37757, N.v37757.
  unfold R.v6, N.v6.
  rewrite ?node_37756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37758 (s : N.State) (i : N.Inputs) :
  R.v37758 (state s) (inputs i) = Zmod.unsigned (N.v37758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37758 s i)) at 1.
  unfold R.v37758, N.v37758.
  rewrite ?node_5237.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37759 (s : N.State) (i : N.Inputs) :
  R.v37759 (state s) (inputs i) = Zmod.unsigned (N.v37759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37759 s i)) at 1.
  unfold R.v37759, N.v37759.
  unfold R.v6, N.v6.
  rewrite ?node_5269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37760 (s : N.State) (i : N.Inputs) :
  R.v37760 (state s) (inputs i) = Zmod.unsigned (N.v37760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37760 s i)) at 1.
  unfold R.v37760, N.v37760.
  rewrite ?node_37758.
  rewrite ?node_37759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37761 (s : N.State) (i : N.Inputs) :
  R.v37761 (state s) (inputs i) = Zmod.unsigned (N.v37761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37761 s i)) at 1.
  unfold R.v37761, N.v37761.
  rewrite ?node_37757.
  rewrite ?node_37760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37762 (s : N.State) (i : N.Inputs) :
  R.v37762 (state s) (inputs i) = Zmod.unsigned (N.v37762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37762 s i)) at 1.
  unfold R.v37762, N.v37762.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37763 (s : N.State) (i : N.Inputs) :
  R.v37763 (state s) (inputs i) = Zmod.unsigned (N.v37763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37763 s i)) at 1.
  unfold R.v37763, N.v37763.
  unfold R.v6, N.v6.
  rewrite ?node_5238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37764 (s : N.State) (i : N.Inputs) :
  R.v37764 (state s) (inputs i) = Zmod.unsigned (N.v37764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37764 s i)) at 1.
  unfold R.v37764, N.v37764.
  unfold R.v6, N.v6.
  rewrite ?node_5237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37765 (s : N.State) (i : N.Inputs) :
  R.v37765 (state s) (inputs i) = Zmod.unsigned (N.v37765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37765 s i)) at 1.
  unfold R.v37765, N.v37765.
  rewrite ?node_37763.
  rewrite ?node_37764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37766 (s : N.State) (i : N.Inputs) :
  R.v37766 (state s) (inputs i) = Zmod.unsigned (N.v37766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37766 s i)) at 1.
  unfold R.v37766, N.v37766.
  unfold R.v16463, N.v16463.
  rewrite ?node_37765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37767 (s : N.State) (i : N.Inputs) :
  R.v37767 (state s) (inputs i) = Zmod.unsigned (N.v37767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37767 s i)) at 1.
  unfold R.v37767, N.v37767.
  rewrite ?node_5239.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37768 (s : N.State) (i : N.Inputs) :
  R.v37768 (state s) (inputs i) = Zmod.unsigned (N.v37768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37768 s i)) at 1.
  unfold R.v37768, N.v37768.
  unfold R.v6, N.v6.
  rewrite ?node_5271.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37769 (s : N.State) (i : N.Inputs) :
  R.v37769 (state s) (inputs i) = Zmod.unsigned (N.v37769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37769 s i)) at 1.
  unfold R.v37769, N.v37769.
  rewrite ?node_37767.
  rewrite ?node_37768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37770 (s : N.State) (i : N.Inputs) :
  R.v37770 (state s) (inputs i) = Zmod.unsigned (N.v37770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37770 s i)) at 1.
  unfold R.v37770, N.v37770.
  rewrite ?node_37766.
  rewrite ?node_37769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37771 (s : N.State) (i : N.Inputs) :
  R.v37771 (state s) (inputs i) = Zmod.unsigned (N.v37771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37771 s i)) at 1.
  unfold R.v37771, N.v37771.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37772 (s : N.State) (i : N.Inputs) :
  R.v37772 (state s) (inputs i) = Zmod.unsigned (N.v37772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37772 s i)) at 1.
  unfold R.v37772, N.v37772.
  rewrite ?node_5269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37773 (s : N.State) (i : N.Inputs) :
  R.v37773 (state s) (inputs i) = Zmod.unsigned (N.v37773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37773 s i)) at 1.
  unfold R.v37773, N.v37773.
  rewrite ?node_5265.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37774 (s : N.State) (i : N.Inputs) :
  R.v37774 (state s) (inputs i) = Zmod.unsigned (N.v37774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37774 s i)) at 1.
  unfold R.v37774, N.v37774.
  rewrite ?node_5263.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37775 (s : N.State) (i : N.Inputs) :
  R.v37775 (state s) (inputs i) = Zmod.unsigned (N.v37775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37775 s i)) at 1.
  unfold R.v37775, N.v37775.
  unfold R.v6, N.v6.
  rewrite ?node_5259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37776 (s : N.State) (i : N.Inputs) :
  R.v37776 (state s) (inputs i) = Zmod.unsigned (N.v37776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37776 s i)) at 1.
  unfold R.v37776, N.v37776.
  unfold R.v6, N.v6.
  rewrite ?node_5257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37777 (s : N.State) (i : N.Inputs) :
  R.v37777 (state s) (inputs i) = Zmod.unsigned (N.v37777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37777 s i)) at 1.
  unfold R.v37777, N.v37777.
  rewrite ?node_37775.
  rewrite ?node_37776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37778 (s : N.State) (i : N.Inputs) :
  R.v37778 (state s) (inputs i) = Zmod.unsigned (N.v37778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37778 s i)) at 1.
  unfold R.v37778, N.v37778.
  unfold R.v16484, N.v16484.
  rewrite ?node_37777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37779 (s : N.State) (i : N.Inputs) :
  R.v37779 (state s) (inputs i) = Zmod.unsigned (N.v37779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37779 s i)) at 1.
  unfold R.v37779, N.v37779.
  rewrite ?node_37772.
  rewrite ?node_37773.
  rewrite ?node_37774.
  rewrite ?node_37778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37780 (s : N.State) (i : N.Inputs) :
  R.v37780 (state s) (inputs i) = Zmod.unsigned (N.v37780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37780 s i)) at 1.
  unfold R.v37780, N.v37780.
  unfold R.v6, N.v6.
  rewrite ?node_37779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37781 (s : N.State) (i : N.Inputs) :
  R.v37781 (state s) (inputs i) = Zmod.unsigned (N.v37781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37781 s i)) at 1.
  unfold R.v37781, N.v37781.
  rewrite ?node_5270.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37782 (s : N.State) (i : N.Inputs) :
  R.v37782 (state s) (inputs i) = Zmod.unsigned (N.v37782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37782 s i)) at 1.
  unfold R.v37782, N.v37782.
  unfold R.v6, N.v6.
  rewrite ?node_5300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37783 (s : N.State) (i : N.Inputs) :
  R.v37783 (state s) (inputs i) = Zmod.unsigned (N.v37783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37783 s i)) at 1.
  unfold R.v37783, N.v37783.
  unfold R.v6, N.v6.
  rewrite ?node_5304.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37784 (s : N.State) (i : N.Inputs) :
  R.v37784 (state s) (inputs i) = Zmod.unsigned (N.v37784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37784 s i)) at 1.
  unfold R.v37784, N.v37784.
  rewrite ?node_37781.
  rewrite ?node_37782.
  rewrite ?node_37783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37785 (s : N.State) (i : N.Inputs) :
  R.v37785 (state s) (inputs i) = Zmod.unsigned (N.v37785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37785 s i)) at 1.
  unfold R.v37785, N.v37785.
  rewrite ?node_37780.
  rewrite ?node_37784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37786 (s : N.State) (i : N.Inputs) :
  R.v37786 (state s) (inputs i) = Zmod.unsigned (N.v37786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37786 s i)) at 1.
  unfold R.v37786, N.v37786.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37787 (s : N.State) (i : N.Inputs) :
  R.v37787 (state s) (inputs i) = Zmod.unsigned (N.v37787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37787 s i)) at 1.
  unfold R.v37787, N.v37787.
  rewrite ?node_5263.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37788 (s : N.State) (i : N.Inputs) :
  R.v37788 (state s) (inputs i) = Zmod.unsigned (N.v37788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37788 s i)) at 1.
  unfold R.v37788, N.v37788.
  unfold R.v6, N.v6.
  rewrite ?node_5259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37789 (s : N.State) (i : N.Inputs) :
  R.v37789 (state s) (inputs i) = Zmod.unsigned (N.v37789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37789 s i)) at 1.
  unfold R.v37789, N.v37789.
  unfold R.v6, N.v6.
  rewrite ?node_5257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37790 (s : N.State) (i : N.Inputs) :
  R.v37790 (state s) (inputs i) = Zmod.unsigned (N.v37790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37790 s i)) at 1.
  unfold R.v37790, N.v37790.
  rewrite ?node_37788.
  rewrite ?node_37789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37791 (s : N.State) (i : N.Inputs) :
  R.v37791 (state s) (inputs i) = Zmod.unsigned (N.v37791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37791 s i)) at 1.
  unfold R.v37791, N.v37791.
  unfold R.v16484, N.v16484.
  rewrite ?node_37790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37792 (s : N.State) (i : N.Inputs) :
  R.v37792 (state s) (inputs i) = Zmod.unsigned (N.v37792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37792 s i)) at 1.
  unfold R.v37792, N.v37792.
  rewrite ?node_37787.
  rewrite ?node_37791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37793 (s : N.State) (i : N.Inputs) :
  R.v37793 (state s) (inputs i) = Zmod.unsigned (N.v37793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37793 s i)) at 1.
  unfold R.v37793, N.v37793.
  unfold R.v6, N.v6.
  rewrite ?node_37792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37794 (s : N.State) (i : N.Inputs) :
  R.v37794 (state s) (inputs i) = Zmod.unsigned (N.v37794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37794 s i)) at 1.
  unfold R.v37794, N.v37794.
  rewrite ?node_5264.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37795 (s : N.State) (i : N.Inputs) :
  R.v37795 (state s) (inputs i) = Zmod.unsigned (N.v37795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37795 s i)) at 1.
  unfold R.v37795, N.v37795.
  unfold R.v6, N.v6.
  rewrite ?node_5300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37796 (s : N.State) (i : N.Inputs) :
  R.v37796 (state s) (inputs i) = Zmod.unsigned (N.v37796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37796 s i)) at 1.
  unfold R.v37796, N.v37796.
  rewrite ?node_37794.
  rewrite ?node_37795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37797 (s : N.State) (i : N.Inputs) :
  R.v37797 (state s) (inputs i) = Zmod.unsigned (N.v37797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37797 s i)) at 1.
  unfold R.v37797, N.v37797.
  rewrite ?node_37793.
  rewrite ?node_37796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37798 (s : N.State) (i : N.Inputs) :
  R.v37798 (state s) (inputs i) = Zmod.unsigned (N.v37798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37798 s i)) at 1.
  unfold R.v37798, N.v37798.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37799 (s : N.State) (i : N.Inputs) :
  R.v37799 (state s) (inputs i) = Zmod.unsigned (N.v37799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37799 s i)) at 1.
  unfold R.v37799, N.v37799.
  rewrite ?node_5269.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37800 (s : N.State) (i : N.Inputs) :
  R.v37800 (state s) (inputs i) = Zmod.unsigned (N.v37800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37800 s i)) at 1.
  unfold R.v37800, N.v37800.
  unfold R.v6, N.v6.
  rewrite ?node_5265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37801 (s : N.State) (i : N.Inputs) :
  R.v37801 (state s) (inputs i) = Zmod.unsigned (N.v37801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37801 s i)) at 1.
  unfold R.v37801, N.v37801.
  unfold R.v6, N.v6.
  rewrite ?node_5264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37802 (s : N.State) (i : N.Inputs) :
  R.v37802 (state s) (inputs i) = Zmod.unsigned (N.v37802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37802 s i)) at 1.
  unfold R.v37802, N.v37802.
  rewrite ?node_37800.
  rewrite ?node_37801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37803 (s : N.State) (i : N.Inputs) :
  R.v37803 (state s) (inputs i) = Zmod.unsigned (N.v37803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37803 s i)) at 1.
  unfold R.v37803, N.v37803.
  unfold R.v16484, N.v16484.
  rewrite ?node_37802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37804 (s : N.State) (i : N.Inputs) :
  R.v37804 (state s) (inputs i) = Zmod.unsigned (N.v37804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37804 s i)) at 1.
  unfold R.v37804, N.v37804.
  rewrite ?node_37799.
  rewrite ?node_37803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37805 (s : N.State) (i : N.Inputs) :
  R.v37805 (state s) (inputs i) = Zmod.unsigned (N.v37805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37805 s i)) at 1.
  unfold R.v37805, N.v37805.
  unfold R.v6, N.v6.
  rewrite ?node_37804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37806 (s : N.State) (i : N.Inputs) :
  R.v37806 (state s) (inputs i) = Zmod.unsigned (N.v37806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37806 s i)) at 1.
  unfold R.v37806, N.v37806.
  rewrite ?node_5270.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37807 (s : N.State) (i : N.Inputs) :
  R.v37807 (state s) (inputs i) = Zmod.unsigned (N.v37807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37807 s i)) at 1.
  unfold R.v37807, N.v37807.
  unfold R.v6, N.v6.
  rewrite ?node_5304.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37808 (s : N.State) (i : N.Inputs) :
  R.v37808 (state s) (inputs i) = Zmod.unsigned (N.v37808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37808 s i)) at 1.
  unfold R.v37808, N.v37808.
  rewrite ?node_37806.
  rewrite ?node_37807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37809 (s : N.State) (i : N.Inputs) :
  R.v37809 (state s) (inputs i) = Zmod.unsigned (N.v37809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37809 s i)) at 1.
  unfold R.v37809, N.v37809.
  rewrite ?node_37805.
  rewrite ?node_37808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37810 (s : N.State) (i : N.Inputs) :
  R.v37810 (state s) (inputs i) = Zmod.unsigned (N.v37810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37810 s i)) at 1.
  unfold R.v37810, N.v37810.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37811 (s : N.State) (i : N.Inputs) :
  R.v37811 (state s) (inputs i) = Zmod.unsigned (N.v37811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37811 s i)) at 1.
  unfold R.v37811, N.v37811.
  rewrite ?node_5300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37812 (s : N.State) (i : N.Inputs) :
  R.v37812 (state s) (inputs i) = Zmod.unsigned (N.v37812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37812 s i)) at 1.
  unfold R.v37812, N.v37812.
  rewrite ?node_5296.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37813 (s : N.State) (i : N.Inputs) :
  R.v37813 (state s) (inputs i) = Zmod.unsigned (N.v37813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37813 s i)) at 1.
  unfold R.v37813, N.v37813.
  rewrite ?node_5292.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37814 (s : N.State) (i : N.Inputs) :
  R.v37814 (state s) (inputs i) = Zmod.unsigned (N.v37814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37814 s i)) at 1.
  unfold R.v37814, N.v37814.
  unfold R.v6, N.v6.
  rewrite ?node_5288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37815 (s : N.State) (i : N.Inputs) :
  R.v37815 (state s) (inputs i) = Zmod.unsigned (N.v37815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37815 s i)) at 1.
  unfold R.v37815, N.v37815.
  unfold R.v6, N.v6.
  rewrite ?node_5286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37816 (s : N.State) (i : N.Inputs) :
  R.v37816 (state s) (inputs i) = Zmod.unsigned (N.v37816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37816 s i)) at 1.
  unfold R.v37816, N.v37816.
  rewrite ?node_37814.
  rewrite ?node_37815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37817 (s : N.State) (i : N.Inputs) :
  R.v37817 (state s) (inputs i) = Zmod.unsigned (N.v37817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37817 s i)) at 1.
  unfold R.v37817, N.v37817.
  unfold R.v16484, N.v16484.
  rewrite ?node_37816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37818 (s : N.State) (i : N.Inputs) :
  R.v37818 (state s) (inputs i) = Zmod.unsigned (N.v37818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37818 s i)) at 1.
  unfold R.v37818, N.v37818.
  rewrite ?node_37811.
  rewrite ?node_37812.
  rewrite ?node_37813.
  rewrite ?node_37817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37819 (s : N.State) (i : N.Inputs) :
  R.v37819 (state s) (inputs i) = Zmod.unsigned (N.v37819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37819 s i)) at 1.
  unfold R.v37819, N.v37819.
  unfold R.v6, N.v6.
  rewrite ?node_37818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37820 (s : N.State) (i : N.Inputs) :
  R.v37820 (state s) (inputs i) = Zmod.unsigned (N.v37820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37820 s i)) at 1.
  unfold R.v37820, N.v37820.
  rewrite ?node_5301.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37821 (s : N.State) (i : N.Inputs) :
  R.v37821 (state s) (inputs i) = Zmod.unsigned (N.v37821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37821 s i)) at 1.
  unfold R.v37821, N.v37821.
  unfold R.v6, N.v6.
  rewrite ?node_5334.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37822 (s : N.State) (i : N.Inputs) :
  R.v37822 (state s) (inputs i) = Zmod.unsigned (N.v37822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37822 s i)) at 1.
  unfold R.v37822, N.v37822.
  unfold R.v6, N.v6.
  rewrite ?node_5338.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37823 (s : N.State) (i : N.Inputs) :
  R.v37823 (state s) (inputs i) = Zmod.unsigned (N.v37823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37823 s i)) at 1.
  unfold R.v37823, N.v37823.
  rewrite ?node_37820.
  rewrite ?node_37821.
  rewrite ?node_37822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37824 (s : N.State) (i : N.Inputs) :
  R.v37824 (state s) (inputs i) = Zmod.unsigned (N.v37824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37824 s i)) at 1.
  unfold R.v37824, N.v37824.
  rewrite ?node_37819.
  rewrite ?node_37823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37825 (s : N.State) (i : N.Inputs) :
  R.v37825 (state s) (inputs i) = Zmod.unsigned (N.v37825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37825 s i)) at 1.
  unfold R.v37825, N.v37825.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37826 (s : N.State) (i : N.Inputs) :
  R.v37826 (state s) (inputs i) = Zmod.unsigned (N.v37826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37826 s i)) at 1.
  unfold R.v37826, N.v37826.
  rewrite ?node_5292.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37827 (s : N.State) (i : N.Inputs) :
  R.v37827 (state s) (inputs i) = Zmod.unsigned (N.v37827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37827 s i)) at 1.
  unfold R.v37827, N.v37827.
  unfold R.v6, N.v6.
  rewrite ?node_5288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37828 (s : N.State) (i : N.Inputs) :
  R.v37828 (state s) (inputs i) = Zmod.unsigned (N.v37828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37828 s i)) at 1.
  unfold R.v37828, N.v37828.
  unfold R.v6, N.v6.
  rewrite ?node_5286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37829 (s : N.State) (i : N.Inputs) :
  R.v37829 (state s) (inputs i) = Zmod.unsigned (N.v37829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37829 s i)) at 1.
  unfold R.v37829, N.v37829.
  rewrite ?node_37827.
  rewrite ?node_37828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37830 (s : N.State) (i : N.Inputs) :
  R.v37830 (state s) (inputs i) = Zmod.unsigned (N.v37830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37830 s i)) at 1.
  unfold R.v37830, N.v37830.
  unfold R.v16484, N.v16484.
  rewrite ?node_37829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37831 (s : N.State) (i : N.Inputs) :
  R.v37831 (state s) (inputs i) = Zmod.unsigned (N.v37831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37831 s i)) at 1.
  unfold R.v37831, N.v37831.
  rewrite ?node_37826.
  rewrite ?node_37830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37832 (s : N.State) (i : N.Inputs) :
  R.v37832 (state s) (inputs i) = Zmod.unsigned (N.v37832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37832 s i)) at 1.
  unfold R.v37832, N.v37832.
  unfold R.v6, N.v6.
  rewrite ?node_37831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37833 (s : N.State) (i : N.Inputs) :
  R.v37833 (state s) (inputs i) = Zmod.unsigned (N.v37833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37833 s i)) at 1.
  unfold R.v37833, N.v37833.
  rewrite ?node_5293.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37834 (s : N.State) (i : N.Inputs) :
  R.v37834 (state s) (inputs i) = Zmod.unsigned (N.v37834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37834 s i)) at 1.
  unfold R.v37834, N.v37834.
  unfold R.v6, N.v6.
  rewrite ?node_5334.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37835 (s : N.State) (i : N.Inputs) :
  R.v37835 (state s) (inputs i) = Zmod.unsigned (N.v37835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37835 s i)) at 1.
  unfold R.v37835, N.v37835.
  rewrite ?node_37833.
  rewrite ?node_37834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37836 (s : N.State) (i : N.Inputs) :
  R.v37836 (state s) (inputs i) = Zmod.unsigned (N.v37836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37836 s i)) at 1.
  unfold R.v37836, N.v37836.
  rewrite ?node_37832.
  rewrite ?node_37835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37837 (s : N.State) (i : N.Inputs) :
  R.v37837 (state s) (inputs i) = Zmod.unsigned (N.v37837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37837 s i)) at 1.
  unfold R.v37837, N.v37837.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37838 (s : N.State) (i : N.Inputs) :
  R.v37838 (state s) (inputs i) = Zmod.unsigned (N.v37838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37838 s i)) at 1.
  unfold R.v37838, N.v37838.
  rewrite ?node_5300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37839 (s : N.State) (i : N.Inputs) :
  R.v37839 (state s) (inputs i) = Zmod.unsigned (N.v37839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37839 s i)) at 1.
  unfold R.v37839, N.v37839.
  unfold R.v6, N.v6.
  rewrite ?node_5296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37840 (s : N.State) (i : N.Inputs) :
  R.v37840 (state s) (inputs i) = Zmod.unsigned (N.v37840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37840 s i)) at 1.
  unfold R.v37840, N.v37840.
  unfold R.v6, N.v6.
  rewrite ?node_5293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37841 (s : N.State) (i : N.Inputs) :
  R.v37841 (state s) (inputs i) = Zmod.unsigned (N.v37841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37841 s i)) at 1.
  unfold R.v37841, N.v37841.
  rewrite ?node_37839.
  rewrite ?node_37840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37842 (s : N.State) (i : N.Inputs) :
  R.v37842 (state s) (inputs i) = Zmod.unsigned (N.v37842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37842 s i)) at 1.
  unfold R.v37842, N.v37842.
  unfold R.v16484, N.v16484.
  rewrite ?node_37841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37843 (s : N.State) (i : N.Inputs) :
  R.v37843 (state s) (inputs i) = Zmod.unsigned (N.v37843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37843 s i)) at 1.
  unfold R.v37843, N.v37843.
  rewrite ?node_37838.
  rewrite ?node_37842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37844 (s : N.State) (i : N.Inputs) :
  R.v37844 (state s) (inputs i) = Zmod.unsigned (N.v37844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37844 s i)) at 1.
  unfold R.v37844, N.v37844.
  unfold R.v6, N.v6.
  rewrite ?node_37843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37845 (s : N.State) (i : N.Inputs) :
  R.v37845 (state s) (inputs i) = Zmod.unsigned (N.v37845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37845 s i)) at 1.
  unfold R.v37845, N.v37845.
  rewrite ?node_5301.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37846 (s : N.State) (i : N.Inputs) :
  R.v37846 (state s) (inputs i) = Zmod.unsigned (N.v37846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37846 s i)) at 1.
  unfold R.v37846, N.v37846.
  unfold R.v6, N.v6.
  rewrite ?node_5338.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37847 (s : N.State) (i : N.Inputs) :
  R.v37847 (state s) (inputs i) = Zmod.unsigned (N.v37847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37847 s i)) at 1.
  unfold R.v37847, N.v37847.
  rewrite ?node_37845.
  rewrite ?node_37846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37848 (s : N.State) (i : N.Inputs) :
  R.v37848 (state s) (inputs i) = Zmod.unsigned (N.v37848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37848 s i)) at 1.
  unfold R.v37848, N.v37848.
  rewrite ?node_37844.
  rewrite ?node_37847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37849 (s : N.State) (i : N.Inputs) :
  R.v37849 (state s) (inputs i) = Zmod.unsigned (N.v37849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37849 s i)) at 1.
  unfold R.v37849, N.v37849.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37850 (s : N.State) (i : N.Inputs) :
  R.v37850 (state s) (inputs i) = Zmod.unsigned (N.v37850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37850 s i)) at 1.
  unfold R.v37850, N.v37850.
  rewrite ?node_5334.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37851 (s : N.State) (i : N.Inputs) :
  R.v37851 (state s) (inputs i) = Zmod.unsigned (N.v37851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37851 s i)) at 1.
  unfold R.v37851, N.v37851.
  rewrite ?node_5330.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37852 (s : N.State) (i : N.Inputs) :
  R.v37852 (state s) (inputs i) = Zmod.unsigned (N.v37852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37852 s i)) at 1.
  unfold R.v37852, N.v37852.
  rewrite ?node_5326.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37853 (s : N.State) (i : N.Inputs) :
  R.v37853 (state s) (inputs i) = Zmod.unsigned (N.v37853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37853 s i)) at 1.
  unfold R.v37853, N.v37853.
  unfold R.v6, N.v6.
  rewrite ?node_5322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37854 (s : N.State) (i : N.Inputs) :
  R.v37854 (state s) (inputs i) = Zmod.unsigned (N.v37854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37854 s i)) at 1.
  unfold R.v37854, N.v37854.
  unfold R.v6, N.v6.
  rewrite ?node_5319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37855 (s : N.State) (i : N.Inputs) :
  R.v37855 (state s) (inputs i) = Zmod.unsigned (N.v37855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37855 s i)) at 1.
  unfold R.v37855, N.v37855.
  rewrite ?node_37853.
  rewrite ?node_37854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37856 (s : N.State) (i : N.Inputs) :
  R.v37856 (state s) (inputs i) = Zmod.unsigned (N.v37856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37856 s i)) at 1.
  unfold R.v37856, N.v37856.
  unfold R.v16484, N.v16484.
  rewrite ?node_37855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37857 (s : N.State) (i : N.Inputs) :
  R.v37857 (state s) (inputs i) = Zmod.unsigned (N.v37857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37857 s i)) at 1.
  unfold R.v37857, N.v37857.
  rewrite ?node_37850.
  rewrite ?node_37851.
  rewrite ?node_37852.
  rewrite ?node_37856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37858 (s : N.State) (i : N.Inputs) :
  R.v37858 (state s) (inputs i) = Zmod.unsigned (N.v37858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37858 s i)) at 1.
  unfold R.v37858, N.v37858.
  unfold R.v6, N.v6.
  rewrite ?node_37857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37859 (s : N.State) (i : N.Inputs) :
  R.v37859 (state s) (inputs i) = Zmod.unsigned (N.v37859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37859 s i)) at 1.
  unfold R.v37859, N.v37859.
  rewrite ?node_5335.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37860 (s : N.State) (i : N.Inputs) :
  R.v37860 (state s) (inputs i) = Zmod.unsigned (N.v37860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37860 s i)) at 1.
  unfold R.v37860, N.v37860.
  unfold R.v6, N.v6.
  rewrite ?node_5370.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37861 (s : N.State) (i : N.Inputs) :
  R.v37861 (state s) (inputs i) = Zmod.unsigned (N.v37861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37861 s i)) at 1.
  unfold R.v37861, N.v37861.
  unfold R.v6, N.v6.
  rewrite ?node_5374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37862 (s : N.State) (i : N.Inputs) :
  R.v37862 (state s) (inputs i) = Zmod.unsigned (N.v37862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37862 s i)) at 1.
  unfold R.v37862, N.v37862.
  rewrite ?node_37859.
  rewrite ?node_37860.
  rewrite ?node_37861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37863 (s : N.State) (i : N.Inputs) :
  R.v37863 (state s) (inputs i) = Zmod.unsigned (N.v37863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37863 s i)) at 1.
  unfold R.v37863, N.v37863.
  rewrite ?node_37858.
  rewrite ?node_37862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37864 (s : N.State) (i : N.Inputs) :
  R.v37864 (state s) (inputs i) = Zmod.unsigned (N.v37864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37864 s i)) at 1.
  unfold R.v37864, N.v37864.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37865 (s : N.State) (i : N.Inputs) :
  R.v37865 (state s) (inputs i) = Zmod.unsigned (N.v37865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37865 s i)) at 1.
  unfold R.v37865, N.v37865.
  rewrite ?node_5326.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37866 (s : N.State) (i : N.Inputs) :
  R.v37866 (state s) (inputs i) = Zmod.unsigned (N.v37866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37866 s i)) at 1.
  unfold R.v37866, N.v37866.
  unfold R.v6, N.v6.
  rewrite ?node_5322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37867 (s : N.State) (i : N.Inputs) :
  R.v37867 (state s) (inputs i) = Zmod.unsigned (N.v37867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37867 s i)) at 1.
  unfold R.v37867, N.v37867.
  unfold R.v6, N.v6.
  rewrite ?node_5319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37868 (s : N.State) (i : N.Inputs) :
  R.v37868 (state s) (inputs i) = Zmod.unsigned (N.v37868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37868 s i)) at 1.
  unfold R.v37868, N.v37868.
  rewrite ?node_37866.
  rewrite ?node_37867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37869 (s : N.State) (i : N.Inputs) :
  R.v37869 (state s) (inputs i) = Zmod.unsigned (N.v37869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37869 s i)) at 1.
  unfold R.v37869, N.v37869.
  unfold R.v16484, N.v16484.
  rewrite ?node_37868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37870 (s : N.State) (i : N.Inputs) :
  R.v37870 (state s) (inputs i) = Zmod.unsigned (N.v37870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37870 s i)) at 1.
  unfold R.v37870, N.v37870.
  rewrite ?node_37865.
  rewrite ?node_37869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37871 (s : N.State) (i : N.Inputs) :
  R.v37871 (state s) (inputs i) = Zmod.unsigned (N.v37871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37871 s i)) at 1.
  unfold R.v37871, N.v37871.
  unfold R.v6, N.v6.
  rewrite ?node_37870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37872 (s : N.State) (i : N.Inputs) :
  R.v37872 (state s) (inputs i) = Zmod.unsigned (N.v37872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37872 s i)) at 1.
  unfold R.v37872, N.v37872.
  rewrite ?node_5327.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37873 (s : N.State) (i : N.Inputs) :
  R.v37873 (state s) (inputs i) = Zmod.unsigned (N.v37873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37873 s i)) at 1.
  unfold R.v37873, N.v37873.
  unfold R.v6, N.v6.
  rewrite ?node_5370.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37874 (s : N.State) (i : N.Inputs) :
  R.v37874 (state s) (inputs i) = Zmod.unsigned (N.v37874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37874 s i)) at 1.
  unfold R.v37874, N.v37874.
  rewrite ?node_37872.
  rewrite ?node_37873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37875 (s : N.State) (i : N.Inputs) :
  R.v37875 (state s) (inputs i) = Zmod.unsigned (N.v37875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37875 s i)) at 1.
  unfold R.v37875, N.v37875.
  rewrite ?node_37871.
  rewrite ?node_37874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37876 (s : N.State) (i : N.Inputs) :
  R.v37876 (state s) (inputs i) = Zmod.unsigned (N.v37876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37876 s i)) at 1.
  unfold R.v37876, N.v37876.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37877 (s : N.State) (i : N.Inputs) :
  R.v37877 (state s) (inputs i) = Zmod.unsigned (N.v37877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37877 s i)) at 1.
  unfold R.v37877, N.v37877.
  rewrite ?node_5334.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37878 (s : N.State) (i : N.Inputs) :
  R.v37878 (state s) (inputs i) = Zmod.unsigned (N.v37878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37878 s i)) at 1.
  unfold R.v37878, N.v37878.
  unfold R.v6, N.v6.
  rewrite ?node_5330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37879 (s : N.State) (i : N.Inputs) :
  R.v37879 (state s) (inputs i) = Zmod.unsigned (N.v37879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37879 s i)) at 1.
  unfold R.v37879, N.v37879.
  unfold R.v6, N.v6.
  rewrite ?node_5327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37880 (s : N.State) (i : N.Inputs) :
  R.v37880 (state s) (inputs i) = Zmod.unsigned (N.v37880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37880 s i)) at 1.
  unfold R.v37880, N.v37880.
  rewrite ?node_37878.
  rewrite ?node_37879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37881 (s : N.State) (i : N.Inputs) :
  R.v37881 (state s) (inputs i) = Zmod.unsigned (N.v37881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37881 s i)) at 1.
  unfold R.v37881, N.v37881.
  unfold R.v16484, N.v16484.
  rewrite ?node_37880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37882 (s : N.State) (i : N.Inputs) :
  R.v37882 (state s) (inputs i) = Zmod.unsigned (N.v37882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37882 s i)) at 1.
  unfold R.v37882, N.v37882.
  rewrite ?node_37877.
  rewrite ?node_37881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37883 (s : N.State) (i : N.Inputs) :
  R.v37883 (state s) (inputs i) = Zmod.unsigned (N.v37883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37883 s i)) at 1.
  unfold R.v37883, N.v37883.
  unfold R.v6, N.v6.
  rewrite ?node_37882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37884 (s : N.State) (i : N.Inputs) :
  R.v37884 (state s) (inputs i) = Zmod.unsigned (N.v37884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37884 s i)) at 1.
  unfold R.v37884, N.v37884.
  rewrite ?node_5335.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37885 (s : N.State) (i : N.Inputs) :
  R.v37885 (state s) (inputs i) = Zmod.unsigned (N.v37885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37885 s i)) at 1.
  unfold R.v37885, N.v37885.
  unfold R.v6, N.v6.
  rewrite ?node_5374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37886 (s : N.State) (i : N.Inputs) :
  R.v37886 (state s) (inputs i) = Zmod.unsigned (N.v37886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37886 s i)) at 1.
  unfold R.v37886, N.v37886.
  rewrite ?node_37884.
  rewrite ?node_37885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37887 (s : N.State) (i : N.Inputs) :
  R.v37887 (state s) (inputs i) = Zmod.unsigned (N.v37887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37887 s i)) at 1.
  unfold R.v37887, N.v37887.
  rewrite ?node_37883.
  rewrite ?node_37886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37888 (s : N.State) (i : N.Inputs) :
  R.v37888 (state s) (inputs i) = Zmod.unsigned (N.v37888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37888 s i)) at 1.
  unfold R.v37888, N.v37888.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37889 (s : N.State) (i : N.Inputs) :
  R.v37889 (state s) (inputs i) = Zmod.unsigned (N.v37889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37889 s i)) at 1.
  unfold R.v37889, N.v37889.
  rewrite ?node_5370.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37890 (s : N.State) (i : N.Inputs) :
  R.v37890 (state s) (inputs i) = Zmod.unsigned (N.v37890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37890 s i)) at 1.
  unfold R.v37890, N.v37890.
  rewrite ?node_5366.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37891 (s : N.State) (i : N.Inputs) :
  R.v37891 (state s) (inputs i) = Zmod.unsigned (N.v37891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37891 s i)) at 1.
  unfold R.v37891, N.v37891.
  rewrite ?node_5364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37892 (s : N.State) (i : N.Inputs) :
  R.v37892 (state s) (inputs i) = Zmod.unsigned (N.v37892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37892 s i)) at 1.
  unfold R.v37892, N.v37892.
  unfold R.v6, N.v6.
  rewrite ?node_5360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37893 (s : N.State) (i : N.Inputs) :
  R.v37893 (state s) (inputs i) = Zmod.unsigned (N.v37893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37893 s i)) at 1.
  unfold R.v37893, N.v37893.
  unfold R.v6, N.v6.
  rewrite ?node_5353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37894 (s : N.State) (i : N.Inputs) :
  R.v37894 (state s) (inputs i) = Zmod.unsigned (N.v37894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37894 s i)) at 1.
  unfold R.v37894, N.v37894.
  rewrite ?node_37892.
  rewrite ?node_37893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37895 (s : N.State) (i : N.Inputs) :
  R.v37895 (state s) (inputs i) = Zmod.unsigned (N.v37895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37895 s i)) at 1.
  unfold R.v37895, N.v37895.
  unfold R.v16484, N.v16484.
  rewrite ?node_37894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37896 (s : N.State) (i : N.Inputs) :
  R.v37896 (state s) (inputs i) = Zmod.unsigned (N.v37896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37896 s i)) at 1.
  unfold R.v37896, N.v37896.
  rewrite ?node_37889.
  rewrite ?node_37890.
  rewrite ?node_37891.
  rewrite ?node_37895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37897 (s : N.State) (i : N.Inputs) :
  R.v37897 (state s) (inputs i) = Zmod.unsigned (N.v37897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37897 s i)) at 1.
  unfold R.v37897, N.v37897.
  unfold R.v6, N.v6.
  rewrite ?node_37896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37898 (s : N.State) (i : N.Inputs) :
  R.v37898 (state s) (inputs i) = Zmod.unsigned (N.v37898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37898 s i)) at 1.
  unfold R.v37898, N.v37898.
  rewrite ?node_5371.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37899 (s : N.State) (i : N.Inputs) :
  R.v37899 (state s) (inputs i) = Zmod.unsigned (N.v37899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37899 s i)) at 1.
  unfold R.v37899, N.v37899.
  unfold R.v6, N.v6.
  rewrite ?node_5405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37900 (s : N.State) (i : N.Inputs) :
  R.v37900 (state s) (inputs i) = Zmod.unsigned (N.v37900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37900 s i)) at 1.
  unfold R.v37900, N.v37900.
  unfold R.v6, N.v6.
  rewrite ?node_5413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37901 (s : N.State) (i : N.Inputs) :
  R.v37901 (state s) (inputs i) = Zmod.unsigned (N.v37901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37901 s i)) at 1.
  unfold R.v37901, N.v37901.
  rewrite ?node_37898.
  rewrite ?node_37899.
  rewrite ?node_37900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37902 (s : N.State) (i : N.Inputs) :
  R.v37902 (state s) (inputs i) = Zmod.unsigned (N.v37902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37902 s i)) at 1.
  unfold R.v37902, N.v37902.
  rewrite ?node_37897.
  rewrite ?node_37901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37903 (s : N.State) (i : N.Inputs) :
  R.v37903 (state s) (inputs i) = Zmod.unsigned (N.v37903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37903 s i)) at 1.
  unfold R.v37903, N.v37903.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37904 (s : N.State) (i : N.Inputs) :
  R.v37904 (state s) (inputs i) = Zmod.unsigned (N.v37904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37904 s i)) at 1.
  unfold R.v37904, N.v37904.
  rewrite ?node_5364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37905 (s : N.State) (i : N.Inputs) :
  R.v37905 (state s) (inputs i) = Zmod.unsigned (N.v37905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37905 s i)) at 1.
  unfold R.v37905, N.v37905.
  unfold R.v6, N.v6.
  rewrite ?node_5360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37906 (s : N.State) (i : N.Inputs) :
  R.v37906 (state s) (inputs i) = Zmod.unsigned (N.v37906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37906 s i)) at 1.
  unfold R.v37906, N.v37906.
  unfold R.v6, N.v6.
  rewrite ?node_5353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37907 (s : N.State) (i : N.Inputs) :
  R.v37907 (state s) (inputs i) = Zmod.unsigned (N.v37907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37907 s i)) at 1.
  unfold R.v37907, N.v37907.
  rewrite ?node_37905.
  rewrite ?node_37906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37908 (s : N.State) (i : N.Inputs) :
  R.v37908 (state s) (inputs i) = Zmod.unsigned (N.v37908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37908 s i)) at 1.
  unfold R.v37908, N.v37908.
  unfold R.v16484, N.v16484.
  rewrite ?node_37907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37909 (s : N.State) (i : N.Inputs) :
  R.v37909 (state s) (inputs i) = Zmod.unsigned (N.v37909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37909 s i)) at 1.
  unfold R.v37909, N.v37909.
  rewrite ?node_37904.
  rewrite ?node_37908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37910 (s : N.State) (i : N.Inputs) :
  R.v37910 (state s) (inputs i) = Zmod.unsigned (N.v37910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37910 s i)) at 1.
  unfold R.v37910, N.v37910.
  unfold R.v6, N.v6.
  rewrite ?node_37909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37911 (s : N.State) (i : N.Inputs) :
  R.v37911 (state s) (inputs i) = Zmod.unsigned (N.v37911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37911 s i)) at 1.
  unfold R.v37911, N.v37911.
  rewrite ?node_5365.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37912 (s : N.State) (i : N.Inputs) :
  R.v37912 (state s) (inputs i) = Zmod.unsigned (N.v37912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37912 s i)) at 1.
  unfold R.v37912, N.v37912.
  unfold R.v6, N.v6.
  rewrite ?node_5405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37913 (s : N.State) (i : N.Inputs) :
  R.v37913 (state s) (inputs i) = Zmod.unsigned (N.v37913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37913 s i)) at 1.
  unfold R.v37913, N.v37913.
  rewrite ?node_37911.
  rewrite ?node_37912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37914 (s : N.State) (i : N.Inputs) :
  R.v37914 (state s) (inputs i) = Zmod.unsigned (N.v37914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37914 s i)) at 1.
  unfold R.v37914, N.v37914.
  rewrite ?node_37910.
  rewrite ?node_37913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37915 (s : N.State) (i : N.Inputs) :
  R.v37915 (state s) (inputs i) = Zmod.unsigned (N.v37915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37915 s i)) at 1.
  unfold R.v37915, N.v37915.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37916 (s : N.State) (i : N.Inputs) :
  R.v37916 (state s) (inputs i) = Zmod.unsigned (N.v37916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37916 s i)) at 1.
  unfold R.v37916, N.v37916.
  rewrite ?node_5370.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37917 (s : N.State) (i : N.Inputs) :
  R.v37917 (state s) (inputs i) = Zmod.unsigned (N.v37917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37917 s i)) at 1.
  unfold R.v37917, N.v37917.
  unfold R.v6, N.v6.
  rewrite ?node_5366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37918 (s : N.State) (i : N.Inputs) :
  R.v37918 (state s) (inputs i) = Zmod.unsigned (N.v37918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37918 s i)) at 1.
  unfold R.v37918, N.v37918.
  unfold R.v6, N.v6.
  rewrite ?node_5365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37919 (s : N.State) (i : N.Inputs) :
  R.v37919 (state s) (inputs i) = Zmod.unsigned (N.v37919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37919 s i)) at 1.
  unfold R.v37919, N.v37919.
  rewrite ?node_37917.
  rewrite ?node_37918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37920 (s : N.State) (i : N.Inputs) :
  R.v37920 (state s) (inputs i) = Zmod.unsigned (N.v37920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37920 s i)) at 1.
  unfold R.v37920, N.v37920.
  unfold R.v16484, N.v16484.
  rewrite ?node_37919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37921 (s : N.State) (i : N.Inputs) :
  R.v37921 (state s) (inputs i) = Zmod.unsigned (N.v37921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37921 s i)) at 1.
  unfold R.v37921, N.v37921.
  rewrite ?node_37916.
  rewrite ?node_37920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37922 (s : N.State) (i : N.Inputs) :
  R.v37922 (state s) (inputs i) = Zmod.unsigned (N.v37922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37922 s i)) at 1.
  unfold R.v37922, N.v37922.
  unfold R.v6, N.v6.
  rewrite ?node_37921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37923 (s : N.State) (i : N.Inputs) :
  R.v37923 (state s) (inputs i) = Zmod.unsigned (N.v37923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37923 s i)) at 1.
  unfold R.v37923, N.v37923.
  rewrite ?node_5371.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37924 (s : N.State) (i : N.Inputs) :
  R.v37924 (state s) (inputs i) = Zmod.unsigned (N.v37924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37924 s i)) at 1.
  unfold R.v37924, N.v37924.
  unfold R.v6, N.v6.
  rewrite ?node_5413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37925 (s : N.State) (i : N.Inputs) :
  R.v37925 (state s) (inputs i) = Zmod.unsigned (N.v37925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37925 s i)) at 1.
  unfold R.v37925, N.v37925.
  rewrite ?node_37923.
  rewrite ?node_37924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37926 (s : N.State) (i : N.Inputs) :
  R.v37926 (state s) (inputs i) = Zmod.unsigned (N.v37926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37926 s i)) at 1.
  unfold R.v37926, N.v37926.
  rewrite ?node_37922.
  rewrite ?node_37925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37927 (s : N.State) (i : N.Inputs) :
  R.v37927 (state s) (inputs i) = Zmod.unsigned (N.v37927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37927 s i)) at 1.
  unfold R.v37927, N.v37927.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37928 (s : N.State) (i : N.Inputs) :
  R.v37928 (state s) (inputs i) = Zmod.unsigned (N.v37928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37928 s i)) at 1.
  unfold R.v37928, N.v37928.
  rewrite ?node_5405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37929 (s : N.State) (i : N.Inputs) :
  R.v37929 (state s) (inputs i) = Zmod.unsigned (N.v37929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37929 s i)) at 1.
  unfold R.v37929, N.v37929.
  rewrite ?node_5401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37930 (s : N.State) (i : N.Inputs) :
  R.v37930 (state s) (inputs i) = Zmod.unsigned (N.v37930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37930 s i)) at 1.
  unfold R.v37930, N.v37930.
  unfold R.v16463, N.v16463.
  rewrite !state_r78_nr_5F78.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r78_nr_5F78 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37931 (s : N.State) (i : N.Inputs) :
  R.v37931 (state s) (inputs i) = Zmod.unsigned (N.v37931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37931 s i)) at 1.
  unfold R.v37931, N.v37931.
  unfold R.v6, N.v6.
  rewrite ?node_5396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37932 (s : N.State) (i : N.Inputs) :
  R.v37932 (state s) (inputs i) = Zmod.unsigned (N.v37932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37932 s i)) at 1.
  unfold R.v37932, N.v37932.
  unfold R.v6, N.v6.
  rewrite ?node_5389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37933 (s : N.State) (i : N.Inputs) :
  R.v37933 (state s) (inputs i) = Zmod.unsigned (N.v37933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37933 s i)) at 1.
  unfold R.v37933, N.v37933.
  rewrite ?node_37931.
  rewrite ?node_37932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37934 (s : N.State) (i : N.Inputs) :
  R.v37934 (state s) (inputs i) = Zmod.unsigned (N.v37934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37934 s i)) at 1.
  unfold R.v37934, N.v37934.
  unfold R.v16484, N.v16484.
  rewrite ?node_37933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37935 (s : N.State) (i : N.Inputs) :
  R.v37935 (state s) (inputs i) = Zmod.unsigned (N.v37935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37935 s i)) at 1.
  unfold R.v37935, N.v37935.
  rewrite ?node_37928.
  rewrite ?node_37929.
  rewrite ?node_37930.
  rewrite ?node_37934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37936 (s : N.State) (i : N.Inputs) :
  R.v37936 (state s) (inputs i) = Zmod.unsigned (N.v37936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37936 s i)) at 1.
  unfold R.v37936, N.v37936.
  unfold R.v6, N.v6.
  rewrite ?node_37935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37937 (s : N.State) (i : N.Inputs) :
  R.v37937 (state s) (inputs i) = Zmod.unsigned (N.v37937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37937 s i)) at 1.
  unfold R.v37937, N.v37937.
  rewrite ?node_5406.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37938 (s : N.State) (i : N.Inputs) :
  R.v37938 (state s) (inputs i) = Zmod.unsigned (N.v37938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37938 s i)) at 1.
  unfold R.v37938, N.v37938.
  unfold R.v6, N.v6.
  rewrite ?node_5444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37939 (s : N.State) (i : N.Inputs) :
  R.v37939 (state s) (inputs i) = Zmod.unsigned (N.v37939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37939 s i)) at 1.
  unfold R.v37939, N.v37939.
  unfold R.v6, N.v6.
  rewrite ?node_5452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37940 (s : N.State) (i : N.Inputs) :
  R.v37940 (state s) (inputs i) = Zmod.unsigned (N.v37940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37940 s i)) at 1.
  unfold R.v37940, N.v37940.
  rewrite ?node_37937.
  rewrite ?node_37938.
  rewrite ?node_37939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37941 (s : N.State) (i : N.Inputs) :
  R.v37941 (state s) (inputs i) = Zmod.unsigned (N.v37941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37941 s i)) at 1.
  unfold R.v37941, N.v37941.
  rewrite ?node_37936.
  rewrite ?node_37940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37942 (s : N.State) (i : N.Inputs) :
  R.v37942 (state s) (inputs i) = Zmod.unsigned (N.v37942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37942 s i)) at 1.
  unfold R.v37942, N.v37942.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37943 (s : N.State) (i : N.Inputs) :
  R.v37943 (state s) (inputs i) = Zmod.unsigned (N.v37943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37943 s i)) at 1.
  unfold R.v37943, N.v37943.
  unfold R.v16463, N.v16463.
  rewrite !state_r78_nr_5F78.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r78_nr_5F78 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37944 (s : N.State) (i : N.Inputs) :
  R.v37944 (state s) (inputs i) = Zmod.unsigned (N.v37944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37944 s i)) at 1.
  unfold R.v37944, N.v37944.
  unfold R.v6, N.v6.
  rewrite ?node_5396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37945 (s : N.State) (i : N.Inputs) :
  R.v37945 (state s) (inputs i) = Zmod.unsigned (N.v37945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37945 s i)) at 1.
  unfold R.v37945, N.v37945.
  unfold R.v6, N.v6.
  rewrite ?node_5389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37946 (s : N.State) (i : N.Inputs) :
  R.v37946 (state s) (inputs i) = Zmod.unsigned (N.v37946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37946 s i)) at 1.
  unfold R.v37946, N.v37946.
  rewrite ?node_37944.
  rewrite ?node_37945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37947 (s : N.State) (i : N.Inputs) :
  R.v37947 (state s) (inputs i) = Zmod.unsigned (N.v37947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37947 s i)) at 1.
  unfold R.v37947, N.v37947.
  unfold R.v16484, N.v16484.
  rewrite ?node_37946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37948 (s : N.State) (i : N.Inputs) :
  R.v37948 (state s) (inputs i) = Zmod.unsigned (N.v37948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37948 s i)) at 1.
  unfold R.v37948, N.v37948.
  rewrite ?node_37943.
  rewrite ?node_37947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37949 (s : N.State) (i : N.Inputs) :
  R.v37949 (state s) (inputs i) = Zmod.unsigned (N.v37949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37949 s i)) at 1.
  unfold R.v37949, N.v37949.
  unfold R.v6, N.v6.
  rewrite ?node_37948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37950 (s : N.State) (i : N.Inputs) :
  R.v37950 (state s) (inputs i) = Zmod.unsigned (N.v37950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37950 s i)) at 1.
  unfold R.v37950, N.v37950.
  rewrite ?node_5398.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37951 (s : N.State) (i : N.Inputs) :
  R.v37951 (state s) (inputs i) = Zmod.unsigned (N.v37951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37951 s i)) at 1.
  unfold R.v37951, N.v37951.
  unfold R.v6, N.v6.
  rewrite ?node_5444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37952 (s : N.State) (i : N.Inputs) :
  R.v37952 (state s) (inputs i) = Zmod.unsigned (N.v37952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37952 s i)) at 1.
  unfold R.v37952, N.v37952.
  rewrite ?node_37950.
  rewrite ?node_37951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37953 (s : N.State) (i : N.Inputs) :
  R.v37953 (state s) (inputs i) = Zmod.unsigned (N.v37953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37953 s i)) at 1.
  unfold R.v37953, N.v37953.
  rewrite ?node_37949.
  rewrite ?node_37952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37954 (s : N.State) (i : N.Inputs) :
  R.v37954 (state s) (inputs i) = Zmod.unsigned (N.v37954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37954 s i)) at 1.
  unfold R.v37954, N.v37954.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37955 (s : N.State) (i : N.Inputs) :
  R.v37955 (state s) (inputs i) = Zmod.unsigned (N.v37955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37955 s i)) at 1.
  unfold R.v37955, N.v37955.
  rewrite ?node_5405.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37956 (s : N.State) (i : N.Inputs) :
  R.v37956 (state s) (inputs i) = Zmod.unsigned (N.v37956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37956 s i)) at 1.
  unfold R.v37956, N.v37956.
  unfold R.v6, N.v6.
  rewrite ?node_5401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37957 (s : N.State) (i : N.Inputs) :
  R.v37957 (state s) (inputs i) = Zmod.unsigned (N.v37957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37957 s i)) at 1.
  unfold R.v37957, N.v37957.
  unfold R.v6, N.v6.
  rewrite ?node_5398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37958 (s : N.State) (i : N.Inputs) :
  R.v37958 (state s) (inputs i) = Zmod.unsigned (N.v37958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37958 s i)) at 1.
  unfold R.v37958, N.v37958.
  rewrite ?node_37956.
  rewrite ?node_37957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37959 (s : N.State) (i : N.Inputs) :
  R.v37959 (state s) (inputs i) = Zmod.unsigned (N.v37959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37959 s i)) at 1.
  unfold R.v37959, N.v37959.
  unfold R.v16484, N.v16484.
  rewrite ?node_37958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37960 (s : N.State) (i : N.Inputs) :
  R.v37960 (state s) (inputs i) = Zmod.unsigned (N.v37960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37960 s i)) at 1.
  unfold R.v37960, N.v37960.
  rewrite ?node_37955.
  rewrite ?node_37959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37961 (s : N.State) (i : N.Inputs) :
  R.v37961 (state s) (inputs i) = Zmod.unsigned (N.v37961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37961 s i)) at 1.
  unfold R.v37961, N.v37961.
  unfold R.v6, N.v6.
  rewrite ?node_37960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37962 (s : N.State) (i : N.Inputs) :
  R.v37962 (state s) (inputs i) = Zmod.unsigned (N.v37962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37962 s i)) at 1.
  unfold R.v37962, N.v37962.
  rewrite ?node_5406.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37963 (s : N.State) (i : N.Inputs) :
  R.v37963 (state s) (inputs i) = Zmod.unsigned (N.v37963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37963 s i)) at 1.
  unfold R.v37963, N.v37963.
  unfold R.v6, N.v6.
  rewrite ?node_5452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37964 (s : N.State) (i : N.Inputs) :
  R.v37964 (state s) (inputs i) = Zmod.unsigned (N.v37964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37964 s i)) at 1.
  unfold R.v37964, N.v37964.
  rewrite ?node_37962.
  rewrite ?node_37963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37965 (s : N.State) (i : N.Inputs) :
  R.v37965 (state s) (inputs i) = Zmod.unsigned (N.v37965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37965 s i)) at 1.
  unfold R.v37965, N.v37965.
  rewrite ?node_37961.
  rewrite ?node_37964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37966 (s : N.State) (i : N.Inputs) :
  R.v37966 (state s) (inputs i) = Zmod.unsigned (N.v37966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37966 s i)) at 1.
  unfold R.v37966, N.v37966.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37967 (s : N.State) (i : N.Inputs) :
  R.v37967 (state s) (inputs i) = Zmod.unsigned (N.v37967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37967 s i)) at 1.
  unfold R.v37967, N.v37967.
  rewrite ?node_5444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37968 (s : N.State) (i : N.Inputs) :
  R.v37968 (state s) (inputs i) = Zmod.unsigned (N.v37968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37968 s i)) at 1.
  unfold R.v37968, N.v37968.
  rewrite ?node_5440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37969 (s : N.State) (i : N.Inputs) :
  R.v37969 (state s) (inputs i) = Zmod.unsigned (N.v37969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37969 s i)) at 1.
  unfold R.v37969, N.v37969.
  unfold R.v16463, N.v16463.
  rewrite !state_r87_nr_5F87.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r87_nr_5F87 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37970 (s : N.State) (i : N.Inputs) :
  R.v37970 (state s) (inputs i) = Zmod.unsigned (N.v37970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37970 s i)) at 1.
  unfold R.v37970, N.v37970.
  unfold R.v6, N.v6.
  rewrite ?node_5435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37971 (s : N.State) (i : N.Inputs) :
  R.v37971 (state s) (inputs i) = Zmod.unsigned (N.v37971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37971 s i)) at 1.
  unfold R.v37971, N.v37971.
  unfold R.v6, N.v6.
  rewrite ?node_5428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37972 (s : N.State) (i : N.Inputs) :
  R.v37972 (state s) (inputs i) = Zmod.unsigned (N.v37972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37972 s i)) at 1.
  unfold R.v37972, N.v37972.
  rewrite ?node_37970.
  rewrite ?node_37971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37973 (s : N.State) (i : N.Inputs) :
  R.v37973 (state s) (inputs i) = Zmod.unsigned (N.v37973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37973 s i)) at 1.
  unfold R.v37973, N.v37973.
  unfold R.v16484, N.v16484.
  rewrite ?node_37972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37974 (s : N.State) (i : N.Inputs) :
  R.v37974 (state s) (inputs i) = Zmod.unsigned (N.v37974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37974 s i)) at 1.
  unfold R.v37974, N.v37974.
  rewrite ?node_37967.
  rewrite ?node_37968.
  rewrite ?node_37969.
  rewrite ?node_37973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37975 (s : N.State) (i : N.Inputs) :
  R.v37975 (state s) (inputs i) = Zmod.unsigned (N.v37975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37975 s i)) at 1.
  unfold R.v37975, N.v37975.
  unfold R.v6, N.v6.
  rewrite ?node_37974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37976 (s : N.State) (i : N.Inputs) :
  R.v37976 (state s) (inputs i) = Zmod.unsigned (N.v37976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37976 s i)) at 1.
  unfold R.v37976, N.v37976.
  rewrite ?node_5445.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37977 (s : N.State) (i : N.Inputs) :
  R.v37977 (state s) (inputs i) = Zmod.unsigned (N.v37977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37977 s i)) at 1.
  unfold R.v37977, N.v37977.
  unfold R.v6, N.v6.
  rewrite ?node_5486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37978 (s : N.State) (i : N.Inputs) :
  R.v37978 (state s) (inputs i) = Zmod.unsigned (N.v37978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37978 s i)) at 1.
  unfold R.v37978, N.v37978.
  unfold R.v6, N.v6.
  rewrite ?node_5494.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37979 (s : N.State) (i : N.Inputs) :
  R.v37979 (state s) (inputs i) = Zmod.unsigned (N.v37979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37979 s i)) at 1.
  unfold R.v37979, N.v37979.
  rewrite ?node_37976.
  rewrite ?node_37977.
  rewrite ?node_37978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37980 (s : N.State) (i : N.Inputs) :
  R.v37980 (state s) (inputs i) = Zmod.unsigned (N.v37980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37980 s i)) at 1.
  unfold R.v37980, N.v37980.
  rewrite ?node_37975.
  rewrite ?node_37979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37981 (s : N.State) (i : N.Inputs) :
  R.v37981 (state s) (inputs i) = Zmod.unsigned (N.v37981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37981 s i)) at 1.
  unfold R.v37981, N.v37981.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37982 (s : N.State) (i : N.Inputs) :
  R.v37982 (state s) (inputs i) = Zmod.unsigned (N.v37982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37982 s i)) at 1.
  unfold R.v37982, N.v37982.
  unfold R.v16463, N.v16463.
  rewrite !state_r87_nr_5F87.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r87_nr_5F87 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37983 (s : N.State) (i : N.Inputs) :
  R.v37983 (state s) (inputs i) = Zmod.unsigned (N.v37983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37983 s i)) at 1.
  unfold R.v37983, N.v37983.
  unfold R.v6, N.v6.
  rewrite ?node_5435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37984 (s : N.State) (i : N.Inputs) :
  R.v37984 (state s) (inputs i) = Zmod.unsigned (N.v37984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37984 s i)) at 1.
  unfold R.v37984, N.v37984.
  unfold R.v6, N.v6.
  rewrite ?node_5428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37985 (s : N.State) (i : N.Inputs) :
  R.v37985 (state s) (inputs i) = Zmod.unsigned (N.v37985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37985 s i)) at 1.
  unfold R.v37985, N.v37985.
  rewrite ?node_37983.
  rewrite ?node_37984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37986 (s : N.State) (i : N.Inputs) :
  R.v37986 (state s) (inputs i) = Zmod.unsigned (N.v37986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37986 s i)) at 1.
  unfold R.v37986, N.v37986.
  unfold R.v16484, N.v16484.
  rewrite ?node_37985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37987 (s : N.State) (i : N.Inputs) :
  R.v37987 (state s) (inputs i) = Zmod.unsigned (N.v37987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37987 s i)) at 1.
  unfold R.v37987, N.v37987.
  rewrite ?node_37982.
  rewrite ?node_37986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37988 (s : N.State) (i : N.Inputs) :
  R.v37988 (state s) (inputs i) = Zmod.unsigned (N.v37988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37988 s i)) at 1.
  unfold R.v37988, N.v37988.
  unfold R.v6, N.v6.
  rewrite ?node_37987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37989 (s : N.State) (i : N.Inputs) :
  R.v37989 (state s) (inputs i) = Zmod.unsigned (N.v37989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37989 s i)) at 1.
  unfold R.v37989, N.v37989.
  rewrite ?node_5437.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37990 (s : N.State) (i : N.Inputs) :
  R.v37990 (state s) (inputs i) = Zmod.unsigned (N.v37990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37990 s i)) at 1.
  unfold R.v37990, N.v37990.
  unfold R.v6, N.v6.
  rewrite ?node_5486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37991 (s : N.State) (i : N.Inputs) :
  R.v37991 (state s) (inputs i) = Zmod.unsigned (N.v37991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37991 s i)) at 1.
  unfold R.v37991, N.v37991.
  rewrite ?node_37989.
  rewrite ?node_37990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37992 (s : N.State) (i : N.Inputs) :
  R.v37992 (state s) (inputs i) = Zmod.unsigned (N.v37992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37992 s i)) at 1.
  unfold R.v37992, N.v37992.
  rewrite ?node_37988.
  rewrite ?node_37991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37993 (s : N.State) (i : N.Inputs) :
  R.v37993 (state s) (inputs i) = Zmod.unsigned (N.v37993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37993 s i)) at 1.
  unfold R.v37993, N.v37993.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37994 (s : N.State) (i : N.Inputs) :
  R.v37994 (state s) (inputs i) = Zmod.unsigned (N.v37994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37994 s i)) at 1.
  unfold R.v37994, N.v37994.
  rewrite ?node_5444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37995 (s : N.State) (i : N.Inputs) :
  R.v37995 (state s) (inputs i) = Zmod.unsigned (N.v37995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37995 s i)) at 1.
  unfold R.v37995, N.v37995.
  unfold R.v6, N.v6.
  rewrite ?node_5440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37996 (s : N.State) (i : N.Inputs) :
  R.v37996 (state s) (inputs i) = Zmod.unsigned (N.v37996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37996 s i)) at 1.
  unfold R.v37996, N.v37996.
  unfold R.v6, N.v6.
  rewrite ?node_5437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37997 (s : N.State) (i : N.Inputs) :
  R.v37997 (state s) (inputs i) = Zmod.unsigned (N.v37997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37997 s i)) at 1.
  unfold R.v37997, N.v37997.
  rewrite ?node_37995.
  rewrite ?node_37996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37998 (s : N.State) (i : N.Inputs) :
  R.v37998 (state s) (inputs i) = Zmod.unsigned (N.v37998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37998 s i)) at 1.
  unfold R.v37998, N.v37998.
  unfold R.v16484, N.v16484.
  rewrite ?node_37997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37999 (s : N.State) (i : N.Inputs) :
  R.v37999 (state s) (inputs i) = Zmod.unsigned (N.v37999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37999 s i)) at 1.
  unfold R.v37999, N.v37999.
  rewrite ?node_37994.
  rewrite ?node_37998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
