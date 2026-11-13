(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes019.
Lemma node_20000 (s : N.State) (i : N.Inputs) :
  R.v20000 (state s) (inputs i) = Zmod.unsigned (N.v20000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20000 s i)) at 1.
  unfold R.v20000, N.v20000.
  unfold R.v6, N.v6.
  rewrite ?node_6872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20001 (s : N.State) (i : N.Inputs) :
  R.v20001 (state s) (inputs i) = Zmod.unsigned (N.v20001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20001 s i)) at 1.
  unfold R.v20001, N.v20001.
  rewrite ?node_19999.
  rewrite ?node_20000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20002 (s : N.State) (i : N.Inputs) :
  R.v20002 (state s) (inputs i) = Zmod.unsigned (N.v20002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20002 s i)) at 1.
  unfold R.v20002, N.v20002.
  unfold R.v16484, N.v16484.
  rewrite ?node_20001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20003 (s : N.State) (i : N.Inputs) :
  R.v20003 (state s) (inputs i) = Zmod.unsigned (N.v20003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20003 s i)) at 1.
  unfold R.v20003, N.v20003.
  rewrite ?node_19998.
  rewrite ?node_20002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20004 (s : N.State) (i : N.Inputs) :
  R.v20004 (state s) (inputs i) = Zmod.unsigned (N.v20004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20004 s i)) at 1.
  unfold R.v20004, N.v20004.
  unfold R.v6, N.v6.
  rewrite ?node_20003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20005 (s : N.State) (i : N.Inputs) :
  R.v20005 (state s) (inputs i) = Zmod.unsigned (N.v20005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20005 s i)) at 1.
  unfold R.v20005, N.v20005.
  rewrite ?node_6877.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20006 (s : N.State) (i : N.Inputs) :
  R.v20006 (state s) (inputs i) = Zmod.unsigned (N.v20006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20006 s i)) at 1.
  unfold R.v20006, N.v20006.
  unfold R.v6, N.v6.
  rewrite ?node_7012.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20007 (s : N.State) (i : N.Inputs) :
  R.v20007 (state s) (inputs i) = Zmod.unsigned (N.v20007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20007 s i)) at 1.
  unfold R.v20007, N.v20007.
  rewrite ?node_20005.
  rewrite ?node_20006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20008 (s : N.State) (i : N.Inputs) :
  R.v20008 (state s) (inputs i) = Zmod.unsigned (N.v20008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20008 s i)) at 1.
  unfold R.v20008, N.v20008.
  rewrite ?node_20004.
  rewrite ?node_20007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20009 (s : N.State) (i : N.Inputs) :
  R.v20009 (state s) (inputs i) = Zmod.unsigned (N.v20009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20009 s i)) at 1.
  unfold R.v20009, N.v20009.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20010 (s : N.State) (i : N.Inputs) :
  R.v20010 (state s) (inputs i) = Zmod.unsigned (N.v20010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20010 s i)) at 1.
  unfold R.v20010, N.v20010.
  rewrite ?node_6883.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20011 (s : N.State) (i : N.Inputs) :
  R.v20011 (state s) (inputs i) = Zmod.unsigned (N.v20011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20011 s i)) at 1.
  unfold R.v20011, N.v20011.
  unfold R.v16463, N.v16463.
  rewrite !state_r405_nr_5F405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r405_nr_5F405 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20012 (s : N.State) (i : N.Inputs) :
  R.v20012 (state s) (inputs i) = Zmod.unsigned (N.v20012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20012 s i)) at 1.
  unfold R.v20012, N.v20012.
  unfold R.v16463, N.v16463.
  rewrite !state_r404_nr_5F404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r404_nr_5F404 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20013 (s : N.State) (i : N.Inputs) :
  R.v20013 (state s) (inputs i) = Zmod.unsigned (N.v20013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20013 s i)) at 1.
  unfold R.v20013, N.v20013.
  unfold R.v6, N.v6.
  rewrite !state_r403_nr_5F403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r403_nr_5F403 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20014 (s : N.State) (i : N.Inputs) :
  R.v20014 (state s) (inputs i) = Zmod.unsigned (N.v20014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20014 s i)) at 1.
  unfold R.v20014, N.v20014.
  unfold R.v6, N.v6.
  rewrite !state_r402_nr_5F402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r402_nr_5F402 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20015 (s : N.State) (i : N.Inputs) :
  R.v20015 (state s) (inputs i) = Zmod.unsigned (N.v20015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20015 s i)) at 1.
  unfold R.v20015, N.v20015.
  rewrite ?node_20013.
  rewrite ?node_20014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20016 (s : N.State) (i : N.Inputs) :
  R.v20016 (state s) (inputs i) = Zmod.unsigned (N.v20016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20016 s i)) at 1.
  unfold R.v20016, N.v20016.
  unfold R.v16484, N.v16484.
  rewrite ?node_20015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20017 (s : N.State) (i : N.Inputs) :
  R.v20017 (state s) (inputs i) = Zmod.unsigned (N.v20017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20017 s i)) at 1.
  unfold R.v20017, N.v20017.
  rewrite ?node_20010.
  rewrite ?node_20011.
  rewrite ?node_20012.
  rewrite ?node_20016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20018 (s : N.State) (i : N.Inputs) :
  R.v20018 (state s) (inputs i) = Zmod.unsigned (N.v20018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20018 s i)) at 1.
  unfold R.v20018, N.v20018.
  unfold R.v6, N.v6.
  rewrite ?node_20017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20019 (s : N.State) (i : N.Inputs) :
  R.v20019 (state s) (inputs i) = Zmod.unsigned (N.v20019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20019 s i)) at 1.
  unfold R.v20019, N.v20019.
  rewrite ?node_6884.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20020 (s : N.State) (i : N.Inputs) :
  R.v20020 (state s) (inputs i) = Zmod.unsigned (N.v20020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20020 s i)) at 1.
  unfold R.v20020, N.v20020.
  unfold R.v6, N.v6.
  rewrite ?node_6979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20021 (s : N.State) (i : N.Inputs) :
  R.v20021 (state s) (inputs i) = Zmod.unsigned (N.v20021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20021 s i)) at 1.
  unfold R.v20021, N.v20021.
  unfold R.v6, N.v6.
  rewrite ?node_7016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20022 (s : N.State) (i : N.Inputs) :
  R.v20022 (state s) (inputs i) = Zmod.unsigned (N.v20022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20022 s i)) at 1.
  unfold R.v20022, N.v20022.
  rewrite ?node_20019.
  rewrite ?node_20020.
  rewrite ?node_20021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20023 (s : N.State) (i : N.Inputs) :
  R.v20023 (state s) (inputs i) = Zmod.unsigned (N.v20023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20023 s i)) at 1.
  unfold R.v20023, N.v20023.
  rewrite ?node_20018.
  rewrite ?node_20022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20024 (s : N.State) (i : N.Inputs) :
  R.v20024 (state s) (inputs i) = Zmod.unsigned (N.v20024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20024 s i)) at 1.
  unfold R.v20024, N.v20024.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20025 (s : N.State) (i : N.Inputs) :
  R.v20025 (state s) (inputs i) = Zmod.unsigned (N.v20025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20025 s i)) at 1.
  unfold R.v20025, N.v20025.
  unfold R.v16463, N.v16463.
  rewrite !state_r404_nr_5F404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r404_nr_5F404 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20026 (s : N.State) (i : N.Inputs) :
  R.v20026 (state s) (inputs i) = Zmod.unsigned (N.v20026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20026 s i)) at 1.
  unfold R.v20026, N.v20026.
  unfold R.v6, N.v6.
  rewrite !state_r403_nr_5F403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r403_nr_5F403 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20027 (s : N.State) (i : N.Inputs) :
  R.v20027 (state s) (inputs i) = Zmod.unsigned (N.v20027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20027 s i)) at 1.
  unfold R.v20027, N.v20027.
  unfold R.v6, N.v6.
  rewrite !state_r402_nr_5F402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r402_nr_5F402 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20028 (s : N.State) (i : N.Inputs) :
  R.v20028 (state s) (inputs i) = Zmod.unsigned (N.v20028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20028 s i)) at 1.
  unfold R.v20028, N.v20028.
  rewrite ?node_20026.
  rewrite ?node_20027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20029 (s : N.State) (i : N.Inputs) :
  R.v20029 (state s) (inputs i) = Zmod.unsigned (N.v20029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20029 s i)) at 1.
  unfold R.v20029, N.v20029.
  unfold R.v16484, N.v16484.
  rewrite ?node_20028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20030 (s : N.State) (i : N.Inputs) :
  R.v20030 (state s) (inputs i) = Zmod.unsigned (N.v20030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20030 s i)) at 1.
  unfold R.v20030, N.v20030.
  rewrite ?node_20025.
  rewrite ?node_20029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20031 (s : N.State) (i : N.Inputs) :
  R.v20031 (state s) (inputs i) = Zmod.unsigned (N.v20031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20031 s i)) at 1.
  unfold R.v20031, N.v20031.
  unfold R.v6, N.v6.
  rewrite ?node_20030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20032 (s : N.State) (i : N.Inputs) :
  R.v20032 (state s) (inputs i) = Zmod.unsigned (N.v20032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20032 s i)) at 1.
  unfold R.v20032, N.v20032.
  rewrite ?node_6879.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20033 (s : N.State) (i : N.Inputs) :
  R.v20033 (state s) (inputs i) = Zmod.unsigned (N.v20033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20033 s i)) at 1.
  unfold R.v20033, N.v20033.
  unfold R.v6, N.v6.
  rewrite ?node_6979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20034 (s : N.State) (i : N.Inputs) :
  R.v20034 (state s) (inputs i) = Zmod.unsigned (N.v20034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20034 s i)) at 1.
  unfold R.v20034, N.v20034.
  rewrite ?node_20032.
  rewrite ?node_20033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20035 (s : N.State) (i : N.Inputs) :
  R.v20035 (state s) (inputs i) = Zmod.unsigned (N.v20035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20035 s i)) at 1.
  unfold R.v20035, N.v20035.
  rewrite ?node_20031.
  rewrite ?node_20034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20036 (s : N.State) (i : N.Inputs) :
  R.v20036 (state s) (inputs i) = Zmod.unsigned (N.v20036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20036 s i)) at 1.
  unfold R.v20036, N.v20036.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20037 (s : N.State) (i : N.Inputs) :
  R.v20037 (state s) (inputs i) = Zmod.unsigned (N.v20037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20037 s i)) at 1.
  unfold R.v20037, N.v20037.
  rewrite ?node_6883.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20038 (s : N.State) (i : N.Inputs) :
  R.v20038 (state s) (inputs i) = Zmod.unsigned (N.v20038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20038 s i)) at 1.
  unfold R.v20038, N.v20038.
  unfold R.v6, N.v6.
  rewrite !state_r405_nr_5F405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r405_nr_5F405 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20039 (s : N.State) (i : N.Inputs) :
  R.v20039 (state s) (inputs i) = Zmod.unsigned (N.v20039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20039 s i)) at 1.
  unfold R.v20039, N.v20039.
  unfold R.v6, N.v6.
  rewrite ?node_6879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20040 (s : N.State) (i : N.Inputs) :
  R.v20040 (state s) (inputs i) = Zmod.unsigned (N.v20040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20040 s i)) at 1.
  unfold R.v20040, N.v20040.
  rewrite ?node_20038.
  rewrite ?node_20039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20041 (s : N.State) (i : N.Inputs) :
  R.v20041 (state s) (inputs i) = Zmod.unsigned (N.v20041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20041 s i)) at 1.
  unfold R.v20041, N.v20041.
  unfold R.v16484, N.v16484.
  rewrite ?node_20040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20042 (s : N.State) (i : N.Inputs) :
  R.v20042 (state s) (inputs i) = Zmod.unsigned (N.v20042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20042 s i)) at 1.
  unfold R.v20042, N.v20042.
  rewrite ?node_20037.
  rewrite ?node_20041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20043 (s : N.State) (i : N.Inputs) :
  R.v20043 (state s) (inputs i) = Zmod.unsigned (N.v20043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20043 s i)) at 1.
  unfold R.v20043, N.v20043.
  unfold R.v6, N.v6.
  rewrite ?node_20042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20044 (s : N.State) (i : N.Inputs) :
  R.v20044 (state s) (inputs i) = Zmod.unsigned (N.v20044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20044 s i)) at 1.
  unfold R.v20044, N.v20044.
  rewrite ?node_6884.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20045 (s : N.State) (i : N.Inputs) :
  R.v20045 (state s) (inputs i) = Zmod.unsigned (N.v20045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20045 s i)) at 1.
  unfold R.v20045, N.v20045.
  unfold R.v6, N.v6.
  rewrite ?node_7016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20046 (s : N.State) (i : N.Inputs) :
  R.v20046 (state s) (inputs i) = Zmod.unsigned (N.v20046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20046 s i)) at 1.
  unfold R.v20046, N.v20046.
  rewrite ?node_20044.
  rewrite ?node_20045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20047 (s : N.State) (i : N.Inputs) :
  R.v20047 (state s) (inputs i) = Zmod.unsigned (N.v20047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20047 s i)) at 1.
  unfold R.v20047, N.v20047.
  rewrite ?node_20043.
  rewrite ?node_20046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20048 (s : N.State) (i : N.Inputs) :
  R.v20048 (state s) (inputs i) = Zmod.unsigned (N.v20048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20048 s i)) at 1.
  unfold R.v20048, N.v20048.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20049 (s : N.State) (i : N.Inputs) :
  R.v20049 (state s) (inputs i) = Zmod.unsigned (N.v20049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20049 s i)) at 1.
  unfold R.v20049, N.v20049.
  rewrite ?node_6891.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20050 (s : N.State) (i : N.Inputs) :
  R.v20050 (state s) (inputs i) = Zmod.unsigned (N.v20050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20050 s i)) at 1.
  unfold R.v20050, N.v20050.
  unfold R.v16463, N.v16463.
  rewrite !state_r409_nr_5F409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r409_nr_5F409 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20051 (s : N.State) (i : N.Inputs) :
  R.v20051 (state s) (inputs i) = Zmod.unsigned (N.v20051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20051 s i)) at 1.
  unfold R.v20051, N.v20051.
  unfold R.v16463, N.v16463.
  rewrite !state_r408_nr_5F408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r408_nr_5F408 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20052 (s : N.State) (i : N.Inputs) :
  R.v20052 (state s) (inputs i) = Zmod.unsigned (N.v20052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20052 s i)) at 1.
  unfold R.v20052, N.v20052.
  unfold R.v6, N.v6.
  rewrite !state_r407_nr_5F407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r407_nr_5F407 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20053 (s : N.State) (i : N.Inputs) :
  R.v20053 (state s) (inputs i) = Zmod.unsigned (N.v20053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20053 s i)) at 1.
  unfold R.v20053, N.v20053.
  unfold R.v6, N.v6.
  rewrite !state_r406_nr_5F406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r406_nr_5F406 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20054 (s : N.State) (i : N.Inputs) :
  R.v20054 (state s) (inputs i) = Zmod.unsigned (N.v20054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20054 s i)) at 1.
  unfold R.v20054, N.v20054.
  rewrite ?node_20052.
  rewrite ?node_20053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20055 (s : N.State) (i : N.Inputs) :
  R.v20055 (state s) (inputs i) = Zmod.unsigned (N.v20055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20055 s i)) at 1.
  unfold R.v20055, N.v20055.
  unfold R.v16484, N.v16484.
  rewrite ?node_20054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20056 (s : N.State) (i : N.Inputs) :
  R.v20056 (state s) (inputs i) = Zmod.unsigned (N.v20056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20056 s i)) at 1.
  unfold R.v20056, N.v20056.
  rewrite ?node_20049.
  rewrite ?node_20050.
  rewrite ?node_20051.
  rewrite ?node_20055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20057 (s : N.State) (i : N.Inputs) :
  R.v20057 (state s) (inputs i) = Zmod.unsigned (N.v20057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20057 s i)) at 1.
  unfold R.v20057, N.v20057.
  unfold R.v6, N.v6.
  rewrite ?node_20056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20058 (s : N.State) (i : N.Inputs) :
  R.v20058 (state s) (inputs i) = Zmod.unsigned (N.v20058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20058 s i)) at 1.
  unfold R.v20058, N.v20058.
  rewrite ?node_6892.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20059 (s : N.State) (i : N.Inputs) :
  R.v20059 (state s) (inputs i) = Zmod.unsigned (N.v20059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20059 s i)) at 1.
  unfold R.v20059, N.v20059.
  unfold R.v6, N.v6.
  rewrite ?node_6987.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20060 (s : N.State) (i : N.Inputs) :
  R.v20060 (state s) (inputs i) = Zmod.unsigned (N.v20060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20060 s i)) at 1.
  unfold R.v20060, N.v20060.
  unfold R.v6, N.v6.
  rewrite ?node_7025.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20061 (s : N.State) (i : N.Inputs) :
  R.v20061 (state s) (inputs i) = Zmod.unsigned (N.v20061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20061 s i)) at 1.
  unfold R.v20061, N.v20061.
  rewrite ?node_20058.
  rewrite ?node_20059.
  rewrite ?node_20060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20062 (s : N.State) (i : N.Inputs) :
  R.v20062 (state s) (inputs i) = Zmod.unsigned (N.v20062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20062 s i)) at 1.
  unfold R.v20062, N.v20062.
  rewrite ?node_20057.
  rewrite ?node_20061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20063 (s : N.State) (i : N.Inputs) :
  R.v20063 (state s) (inputs i) = Zmod.unsigned (N.v20063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20063 s i)) at 1.
  unfold R.v20063, N.v20063.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20064 (s : N.State) (i : N.Inputs) :
  R.v20064 (state s) (inputs i) = Zmod.unsigned (N.v20064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20064 s i)) at 1.
  unfold R.v20064, N.v20064.
  unfold R.v16463, N.v16463.
  rewrite !state_r408_nr_5F408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r408_nr_5F408 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20065 (s : N.State) (i : N.Inputs) :
  R.v20065 (state s) (inputs i) = Zmod.unsigned (N.v20065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20065 s i)) at 1.
  unfold R.v20065, N.v20065.
  unfold R.v6, N.v6.
  rewrite !state_r407_nr_5F407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r407_nr_5F407 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20066 (s : N.State) (i : N.Inputs) :
  R.v20066 (state s) (inputs i) = Zmod.unsigned (N.v20066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20066 s i)) at 1.
  unfold R.v20066, N.v20066.
  unfold R.v6, N.v6.
  rewrite !state_r406_nr_5F406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r406_nr_5F406 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20067 (s : N.State) (i : N.Inputs) :
  R.v20067 (state s) (inputs i) = Zmod.unsigned (N.v20067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20067 s i)) at 1.
  unfold R.v20067, N.v20067.
  rewrite ?node_20065.
  rewrite ?node_20066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20068 (s : N.State) (i : N.Inputs) :
  R.v20068 (state s) (inputs i) = Zmod.unsigned (N.v20068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20068 s i)) at 1.
  unfold R.v20068, N.v20068.
  unfold R.v16484, N.v16484.
  rewrite ?node_20067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20069 (s : N.State) (i : N.Inputs) :
  R.v20069 (state s) (inputs i) = Zmod.unsigned (N.v20069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20069 s i)) at 1.
  unfold R.v20069, N.v20069.
  rewrite ?node_20064.
  rewrite ?node_20068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20070 (s : N.State) (i : N.Inputs) :
  R.v20070 (state s) (inputs i) = Zmod.unsigned (N.v20070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20070 s i)) at 1.
  unfold R.v20070, N.v20070.
  unfold R.v6, N.v6.
  rewrite ?node_20069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20071 (s : N.State) (i : N.Inputs) :
  R.v20071 (state s) (inputs i) = Zmod.unsigned (N.v20071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20071 s i)) at 1.
  unfold R.v20071, N.v20071.
  rewrite ?node_6887.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20072 (s : N.State) (i : N.Inputs) :
  R.v20072 (state s) (inputs i) = Zmod.unsigned (N.v20072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20072 s i)) at 1.
  unfold R.v20072, N.v20072.
  unfold R.v6, N.v6.
  rewrite ?node_6987.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20073 (s : N.State) (i : N.Inputs) :
  R.v20073 (state s) (inputs i) = Zmod.unsigned (N.v20073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20073 s i)) at 1.
  unfold R.v20073, N.v20073.
  rewrite ?node_20071.
  rewrite ?node_20072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20074 (s : N.State) (i : N.Inputs) :
  R.v20074 (state s) (inputs i) = Zmod.unsigned (N.v20074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20074 s i)) at 1.
  unfold R.v20074, N.v20074.
  rewrite ?node_20070.
  rewrite ?node_20073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20075 (s : N.State) (i : N.Inputs) :
  R.v20075 (state s) (inputs i) = Zmod.unsigned (N.v20075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20075 s i)) at 1.
  unfold R.v20075, N.v20075.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20076 (s : N.State) (i : N.Inputs) :
  R.v20076 (state s) (inputs i) = Zmod.unsigned (N.v20076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20076 s i)) at 1.
  unfold R.v20076, N.v20076.
  rewrite ?node_6891.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20077 (s : N.State) (i : N.Inputs) :
  R.v20077 (state s) (inputs i) = Zmod.unsigned (N.v20077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20077 s i)) at 1.
  unfold R.v20077, N.v20077.
  unfold R.v6, N.v6.
  rewrite !state_r409_nr_5F409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r409_nr_5F409 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20078 (s : N.State) (i : N.Inputs) :
  R.v20078 (state s) (inputs i) = Zmod.unsigned (N.v20078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20078 s i)) at 1.
  unfold R.v20078, N.v20078.
  unfold R.v6, N.v6.
  rewrite ?node_6887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20079 (s : N.State) (i : N.Inputs) :
  R.v20079 (state s) (inputs i) = Zmod.unsigned (N.v20079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20079 s i)) at 1.
  unfold R.v20079, N.v20079.
  rewrite ?node_20077.
  rewrite ?node_20078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20080 (s : N.State) (i : N.Inputs) :
  R.v20080 (state s) (inputs i) = Zmod.unsigned (N.v20080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20080 s i)) at 1.
  unfold R.v20080, N.v20080.
  unfold R.v16484, N.v16484.
  rewrite ?node_20079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20081 (s : N.State) (i : N.Inputs) :
  R.v20081 (state s) (inputs i) = Zmod.unsigned (N.v20081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20081 s i)) at 1.
  unfold R.v20081, N.v20081.
  rewrite ?node_20076.
  rewrite ?node_20080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20082 (s : N.State) (i : N.Inputs) :
  R.v20082 (state s) (inputs i) = Zmod.unsigned (N.v20082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20082 s i)) at 1.
  unfold R.v20082, N.v20082.
  unfold R.v6, N.v6.
  rewrite ?node_20081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20083 (s : N.State) (i : N.Inputs) :
  R.v20083 (state s) (inputs i) = Zmod.unsigned (N.v20083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20083 s i)) at 1.
  unfold R.v20083, N.v20083.
  rewrite ?node_6892.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20084 (s : N.State) (i : N.Inputs) :
  R.v20084 (state s) (inputs i) = Zmod.unsigned (N.v20084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20084 s i)) at 1.
  unfold R.v20084, N.v20084.
  unfold R.v6, N.v6.
  rewrite ?node_7025.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20085 (s : N.State) (i : N.Inputs) :
  R.v20085 (state s) (inputs i) = Zmod.unsigned (N.v20085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20085 s i)) at 1.
  unfold R.v20085, N.v20085.
  rewrite ?node_20083.
  rewrite ?node_20084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20086 (s : N.State) (i : N.Inputs) :
  R.v20086 (state s) (inputs i) = Zmod.unsigned (N.v20086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20086 s i)) at 1.
  unfold R.v20086, N.v20086.
  rewrite ?node_20082.
  rewrite ?node_20085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20087 (s : N.State) (i : N.Inputs) :
  R.v20087 (state s) (inputs i) = Zmod.unsigned (N.v20087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20087 s i)) at 1.
  unfold R.v20087, N.v20087.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20088 (s : N.State) (i : N.Inputs) :
  R.v20088 (state s) (inputs i) = Zmod.unsigned (N.v20088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20088 s i)) at 1.
  unfold R.v20088, N.v20088.
  rewrite ?node_6899.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20089 (s : N.State) (i : N.Inputs) :
  R.v20089 (state s) (inputs i) = Zmod.unsigned (N.v20089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20089 s i)) at 1.
  unfold R.v20089, N.v20089.
  unfold R.v16463, N.v16463.
  rewrite !state_r413_nr_5F413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r413_nr_5F413 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20090 (s : N.State) (i : N.Inputs) :
  R.v20090 (state s) (inputs i) = Zmod.unsigned (N.v20090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20090 s i)) at 1.
  unfold R.v20090, N.v20090.
  unfold R.v16463, N.v16463.
  rewrite !state_r412_nr_5F412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r412_nr_5F412 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20091 (s : N.State) (i : N.Inputs) :
  R.v20091 (state s) (inputs i) = Zmod.unsigned (N.v20091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20091 s i)) at 1.
  unfold R.v20091, N.v20091.
  unfold R.v6, N.v6.
  rewrite !state_r411_nr_5F411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r411_nr_5F411 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20092 (s : N.State) (i : N.Inputs) :
  R.v20092 (state s) (inputs i) = Zmod.unsigned (N.v20092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20092 s i)) at 1.
  unfold R.v20092, N.v20092.
  unfold R.v6, N.v6.
  rewrite !state_r410_nr_5F410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r410_nr_5F410 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20093 (s : N.State) (i : N.Inputs) :
  R.v20093 (state s) (inputs i) = Zmod.unsigned (N.v20093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20093 s i)) at 1.
  unfold R.v20093, N.v20093.
  rewrite ?node_20091.
  rewrite ?node_20092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20094 (s : N.State) (i : N.Inputs) :
  R.v20094 (state s) (inputs i) = Zmod.unsigned (N.v20094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20094 s i)) at 1.
  unfold R.v20094, N.v20094.
  unfold R.v16484, N.v16484.
  rewrite ?node_20093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20095 (s : N.State) (i : N.Inputs) :
  R.v20095 (state s) (inputs i) = Zmod.unsigned (N.v20095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20095 s i)) at 1.
  unfold R.v20095, N.v20095.
  rewrite ?node_20088.
  rewrite ?node_20089.
  rewrite ?node_20090.
  rewrite ?node_20094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20096 (s : N.State) (i : N.Inputs) :
  R.v20096 (state s) (inputs i) = Zmod.unsigned (N.v20096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20096 s i)) at 1.
  unfold R.v20096, N.v20096.
  unfold R.v6, N.v6.
  rewrite ?node_20095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20097 (s : N.State) (i : N.Inputs) :
  R.v20097 (state s) (inputs i) = Zmod.unsigned (N.v20097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20097 s i)) at 1.
  unfold R.v20097, N.v20097.
  rewrite ?node_6900.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20098 (s : N.State) (i : N.Inputs) :
  R.v20098 (state s) (inputs i) = Zmod.unsigned (N.v20098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20098 s i)) at 1.
  unfold R.v20098, N.v20098.
  unfold R.v6, N.v6.
  rewrite ?node_6995.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20099 (s : N.State) (i : N.Inputs) :
  R.v20099 (state s) (inputs i) = Zmod.unsigned (N.v20099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20099 s i)) at 1.
  unfold R.v20099, N.v20099.
  unfold R.v6, N.v6.
  rewrite ?node_7028.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20100 (s : N.State) (i : N.Inputs) :
  R.v20100 (state s) (inputs i) = Zmod.unsigned (N.v20100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20100 s i)) at 1.
  unfold R.v20100, N.v20100.
  rewrite ?node_20097.
  rewrite ?node_20098.
  rewrite ?node_20099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20101 (s : N.State) (i : N.Inputs) :
  R.v20101 (state s) (inputs i) = Zmod.unsigned (N.v20101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20101 s i)) at 1.
  unfold R.v20101, N.v20101.
  rewrite ?node_20096.
  rewrite ?node_20100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20102 (s : N.State) (i : N.Inputs) :
  R.v20102 (state s) (inputs i) = Zmod.unsigned (N.v20102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20102 s i)) at 1.
  unfold R.v20102, N.v20102.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20103 (s : N.State) (i : N.Inputs) :
  R.v20103 (state s) (inputs i) = Zmod.unsigned (N.v20103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20103 s i)) at 1.
  unfold R.v20103, N.v20103.
  unfold R.v16463, N.v16463.
  rewrite !state_r412_nr_5F412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r412_nr_5F412 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20104 (s : N.State) (i : N.Inputs) :
  R.v20104 (state s) (inputs i) = Zmod.unsigned (N.v20104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20104 s i)) at 1.
  unfold R.v20104, N.v20104.
  unfold R.v6, N.v6.
  rewrite !state_r411_nr_5F411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r411_nr_5F411 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20105 (s : N.State) (i : N.Inputs) :
  R.v20105 (state s) (inputs i) = Zmod.unsigned (N.v20105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20105 s i)) at 1.
  unfold R.v20105, N.v20105.
  unfold R.v6, N.v6.
  rewrite !state_r410_nr_5F410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r410_nr_5F410 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20106 (s : N.State) (i : N.Inputs) :
  R.v20106 (state s) (inputs i) = Zmod.unsigned (N.v20106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20106 s i)) at 1.
  unfold R.v20106, N.v20106.
  rewrite ?node_20104.
  rewrite ?node_20105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20107 (s : N.State) (i : N.Inputs) :
  R.v20107 (state s) (inputs i) = Zmod.unsigned (N.v20107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20107 s i)) at 1.
  unfold R.v20107, N.v20107.
  unfold R.v16484, N.v16484.
  rewrite ?node_20106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20108 (s : N.State) (i : N.Inputs) :
  R.v20108 (state s) (inputs i) = Zmod.unsigned (N.v20108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20108 s i)) at 1.
  unfold R.v20108, N.v20108.
  rewrite ?node_20103.
  rewrite ?node_20107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20109 (s : N.State) (i : N.Inputs) :
  R.v20109 (state s) (inputs i) = Zmod.unsigned (N.v20109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20109 s i)) at 1.
  unfold R.v20109, N.v20109.
  unfold R.v6, N.v6.
  rewrite ?node_20108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20110 (s : N.State) (i : N.Inputs) :
  R.v20110 (state s) (inputs i) = Zmod.unsigned (N.v20110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20110 s i)) at 1.
  unfold R.v20110, N.v20110.
  rewrite ?node_6895.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20111 (s : N.State) (i : N.Inputs) :
  R.v20111 (state s) (inputs i) = Zmod.unsigned (N.v20111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20111 s i)) at 1.
  unfold R.v20111, N.v20111.
  unfold R.v6, N.v6.
  rewrite ?node_6995.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20112 (s : N.State) (i : N.Inputs) :
  R.v20112 (state s) (inputs i) = Zmod.unsigned (N.v20112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20112 s i)) at 1.
  unfold R.v20112, N.v20112.
  rewrite ?node_20110.
  rewrite ?node_20111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20113 (s : N.State) (i : N.Inputs) :
  R.v20113 (state s) (inputs i) = Zmod.unsigned (N.v20113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20113 s i)) at 1.
  unfold R.v20113, N.v20113.
  rewrite ?node_20109.
  rewrite ?node_20112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20114 (s : N.State) (i : N.Inputs) :
  R.v20114 (state s) (inputs i) = Zmod.unsigned (N.v20114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20114 s i)) at 1.
  unfold R.v20114, N.v20114.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20115 (s : N.State) (i : N.Inputs) :
  R.v20115 (state s) (inputs i) = Zmod.unsigned (N.v20115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20115 s i)) at 1.
  unfold R.v20115, N.v20115.
  rewrite ?node_6899.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20116 (s : N.State) (i : N.Inputs) :
  R.v20116 (state s) (inputs i) = Zmod.unsigned (N.v20116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20116 s i)) at 1.
  unfold R.v20116, N.v20116.
  unfold R.v6, N.v6.
  rewrite !state_r413_nr_5F413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r413_nr_5F413 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20117 (s : N.State) (i : N.Inputs) :
  R.v20117 (state s) (inputs i) = Zmod.unsigned (N.v20117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20117 s i)) at 1.
  unfold R.v20117, N.v20117.
  unfold R.v6, N.v6.
  rewrite ?node_6895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20118 (s : N.State) (i : N.Inputs) :
  R.v20118 (state s) (inputs i) = Zmod.unsigned (N.v20118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20118 s i)) at 1.
  unfold R.v20118, N.v20118.
  rewrite ?node_20116.
  rewrite ?node_20117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20119 (s : N.State) (i : N.Inputs) :
  R.v20119 (state s) (inputs i) = Zmod.unsigned (N.v20119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20119 s i)) at 1.
  unfold R.v20119, N.v20119.
  unfold R.v16484, N.v16484.
  rewrite ?node_20118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20120 (s : N.State) (i : N.Inputs) :
  R.v20120 (state s) (inputs i) = Zmod.unsigned (N.v20120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20120 s i)) at 1.
  unfold R.v20120, N.v20120.
  rewrite ?node_20115.
  rewrite ?node_20119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20121 (s : N.State) (i : N.Inputs) :
  R.v20121 (state s) (inputs i) = Zmod.unsigned (N.v20121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20121 s i)) at 1.
  unfold R.v20121, N.v20121.
  unfold R.v6, N.v6.
  rewrite ?node_20120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20122 (s : N.State) (i : N.Inputs) :
  R.v20122 (state s) (inputs i) = Zmod.unsigned (N.v20122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20122 s i)) at 1.
  unfold R.v20122, N.v20122.
  rewrite ?node_6900.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20123 (s : N.State) (i : N.Inputs) :
  R.v20123 (state s) (inputs i) = Zmod.unsigned (N.v20123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20123 s i)) at 1.
  unfold R.v20123, N.v20123.
  unfold R.v6, N.v6.
  rewrite ?node_7028.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20124 (s : N.State) (i : N.Inputs) :
  R.v20124 (state s) (inputs i) = Zmod.unsigned (N.v20124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20124 s i)) at 1.
  unfold R.v20124, N.v20124.
  rewrite ?node_20122.
  rewrite ?node_20123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20125 (s : N.State) (i : N.Inputs) :
  R.v20125 (state s) (inputs i) = Zmod.unsigned (N.v20125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20125 s i)) at 1.
  unfold R.v20125, N.v20125.
  rewrite ?node_20121.
  rewrite ?node_20124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20126 (s : N.State) (i : N.Inputs) :
  R.v20126 (state s) (inputs i) = Zmod.unsigned (N.v20126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20126 s i)) at 1.
  unfold R.v20126, N.v20126.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20127 (s : N.State) (i : N.Inputs) :
  R.v20127 (state s) (inputs i) = Zmod.unsigned (N.v20127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20127 s i)) at 1.
  unfold R.v20127, N.v20127.
  rewrite ?node_6911.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20128 (s : N.State) (i : N.Inputs) :
  R.v20128 (state s) (inputs i) = Zmod.unsigned (N.v20128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20128 s i)) at 1.
  unfold R.v20128, N.v20128.
  unfold R.v16463, N.v16463.
  rewrite !state_r417_nr_5F417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r417_nr_5F417 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20129 (s : N.State) (i : N.Inputs) :
  R.v20129 (state s) (inputs i) = Zmod.unsigned (N.v20129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20129 s i)) at 1.
  unfold R.v20129, N.v20129.
  unfold R.v16463, N.v16463.
  rewrite !state_r416_nr_5F416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r416_nr_5F416 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20130 (s : N.State) (i : N.Inputs) :
  R.v20130 (state s) (inputs i) = Zmod.unsigned (N.v20130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20130 s i)) at 1.
  unfold R.v20130, N.v20130.
  unfold R.v6, N.v6.
  rewrite !state_r415_nr_5F415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r415_nr_5F415 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20131 (s : N.State) (i : N.Inputs) :
  R.v20131 (state s) (inputs i) = Zmod.unsigned (N.v20131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20131 s i)) at 1.
  unfold R.v20131, N.v20131.
  unfold R.v6, N.v6.
  rewrite !state_r414_nr_5F414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r414_nr_5F414 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20132 (s : N.State) (i : N.Inputs) :
  R.v20132 (state s) (inputs i) = Zmod.unsigned (N.v20132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20132 s i)) at 1.
  unfold R.v20132, N.v20132.
  rewrite ?node_20130.
  rewrite ?node_20131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20133 (s : N.State) (i : N.Inputs) :
  R.v20133 (state s) (inputs i) = Zmod.unsigned (N.v20133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20133 s i)) at 1.
  unfold R.v20133, N.v20133.
  unfold R.v16484, N.v16484.
  rewrite ?node_20132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20134 (s : N.State) (i : N.Inputs) :
  R.v20134 (state s) (inputs i) = Zmod.unsigned (N.v20134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20134 s i)) at 1.
  unfold R.v20134, N.v20134.
  rewrite ?node_20127.
  rewrite ?node_20128.
  rewrite ?node_20129.
  rewrite ?node_20133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20135 (s : N.State) (i : N.Inputs) :
  R.v20135 (state s) (inputs i) = Zmod.unsigned (N.v20135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20135 s i)) at 1.
  unfold R.v20135, N.v20135.
  unfold R.v6, N.v6.
  rewrite ?node_20134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20136 (s : N.State) (i : N.Inputs) :
  R.v20136 (state s) (inputs i) = Zmod.unsigned (N.v20136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20136 s i)) at 1.
  unfold R.v20136, N.v20136.
  rewrite ?node_6912.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20137 (s : N.State) (i : N.Inputs) :
  R.v20137 (state s) (inputs i) = Zmod.unsigned (N.v20137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20137 s i)) at 1.
  unfold R.v20137, N.v20137.
  unfold R.v6, N.v6.
  rewrite ?node_7007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20138 (s : N.State) (i : N.Inputs) :
  R.v20138 (state s) (inputs i) = Zmod.unsigned (N.v20138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20138 s i)) at 1.
  unfold R.v20138, N.v20138.
  unfold R.v6, N.v6.
  rewrite ?node_7032.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20139 (s : N.State) (i : N.Inputs) :
  R.v20139 (state s) (inputs i) = Zmod.unsigned (N.v20139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20139 s i)) at 1.
  unfold R.v20139, N.v20139.
  rewrite ?node_20136.
  rewrite ?node_20137.
  rewrite ?node_20138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20140 (s : N.State) (i : N.Inputs) :
  R.v20140 (state s) (inputs i) = Zmod.unsigned (N.v20140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20140 s i)) at 1.
  unfold R.v20140, N.v20140.
  rewrite ?node_20135.
  rewrite ?node_20139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20141 (s : N.State) (i : N.Inputs) :
  R.v20141 (state s) (inputs i) = Zmod.unsigned (N.v20141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20141 s i)) at 1.
  unfold R.v20141, N.v20141.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20142 (s : N.State) (i : N.Inputs) :
  R.v20142 (state s) (inputs i) = Zmod.unsigned (N.v20142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20142 s i)) at 1.
  unfold R.v20142, N.v20142.
  unfold R.v16463, N.v16463.
  rewrite !state_r416_nr_5F416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r416_nr_5F416 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20143 (s : N.State) (i : N.Inputs) :
  R.v20143 (state s) (inputs i) = Zmod.unsigned (N.v20143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20143 s i)) at 1.
  unfold R.v20143, N.v20143.
  unfold R.v6, N.v6.
  rewrite !state_r415_nr_5F415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r415_nr_5F415 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20144 (s : N.State) (i : N.Inputs) :
  R.v20144 (state s) (inputs i) = Zmod.unsigned (N.v20144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20144 s i)) at 1.
  unfold R.v20144, N.v20144.
  unfold R.v6, N.v6.
  rewrite !state_r414_nr_5F414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r414_nr_5F414 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20145 (s : N.State) (i : N.Inputs) :
  R.v20145 (state s) (inputs i) = Zmod.unsigned (N.v20145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20145 s i)) at 1.
  unfold R.v20145, N.v20145.
  rewrite ?node_20143.
  rewrite ?node_20144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20146 (s : N.State) (i : N.Inputs) :
  R.v20146 (state s) (inputs i) = Zmod.unsigned (N.v20146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20146 s i)) at 1.
  unfold R.v20146, N.v20146.
  unfold R.v16484, N.v16484.
  rewrite ?node_20145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20147 (s : N.State) (i : N.Inputs) :
  R.v20147 (state s) (inputs i) = Zmod.unsigned (N.v20147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20147 s i)) at 1.
  unfold R.v20147, N.v20147.
  rewrite ?node_20142.
  rewrite ?node_20146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20148 (s : N.State) (i : N.Inputs) :
  R.v20148 (state s) (inputs i) = Zmod.unsigned (N.v20148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20148 s i)) at 1.
  unfold R.v20148, N.v20148.
  unfold R.v6, N.v6.
  rewrite ?node_20147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20149 (s : N.State) (i : N.Inputs) :
  R.v20149 (state s) (inputs i) = Zmod.unsigned (N.v20149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20149 s i)) at 1.
  unfold R.v20149, N.v20149.
  rewrite ?node_6907.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20150 (s : N.State) (i : N.Inputs) :
  R.v20150 (state s) (inputs i) = Zmod.unsigned (N.v20150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20150 s i)) at 1.
  unfold R.v20150, N.v20150.
  unfold R.v6, N.v6.
  rewrite ?node_7007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20151 (s : N.State) (i : N.Inputs) :
  R.v20151 (state s) (inputs i) = Zmod.unsigned (N.v20151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20151 s i)) at 1.
  unfold R.v20151, N.v20151.
  rewrite ?node_20149.
  rewrite ?node_20150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20152 (s : N.State) (i : N.Inputs) :
  R.v20152 (state s) (inputs i) = Zmod.unsigned (N.v20152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20152 s i)) at 1.
  unfold R.v20152, N.v20152.
  rewrite ?node_20148.
  rewrite ?node_20151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20153 (s : N.State) (i : N.Inputs) :
  R.v20153 (state s) (inputs i) = Zmod.unsigned (N.v20153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20153 s i)) at 1.
  unfold R.v20153, N.v20153.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20154 (s : N.State) (i : N.Inputs) :
  R.v20154 (state s) (inputs i) = Zmod.unsigned (N.v20154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20154 s i)) at 1.
  unfold R.v20154, N.v20154.
  rewrite ?node_6911.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20155 (s : N.State) (i : N.Inputs) :
  R.v20155 (state s) (inputs i) = Zmod.unsigned (N.v20155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20155 s i)) at 1.
  unfold R.v20155, N.v20155.
  unfold R.v6, N.v6.
  rewrite !state_r417_nr_5F417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r417_nr_5F417 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20156 (s : N.State) (i : N.Inputs) :
  R.v20156 (state s) (inputs i) = Zmod.unsigned (N.v20156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20156 s i)) at 1.
  unfold R.v20156, N.v20156.
  unfold R.v6, N.v6.
  rewrite ?node_6907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20157 (s : N.State) (i : N.Inputs) :
  R.v20157 (state s) (inputs i) = Zmod.unsigned (N.v20157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20157 s i)) at 1.
  unfold R.v20157, N.v20157.
  rewrite ?node_20155.
  rewrite ?node_20156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20158 (s : N.State) (i : N.Inputs) :
  R.v20158 (state s) (inputs i) = Zmod.unsigned (N.v20158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20158 s i)) at 1.
  unfold R.v20158, N.v20158.
  unfold R.v16484, N.v16484.
  rewrite ?node_20157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20159 (s : N.State) (i : N.Inputs) :
  R.v20159 (state s) (inputs i) = Zmod.unsigned (N.v20159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20159 s i)) at 1.
  unfold R.v20159, N.v20159.
  rewrite ?node_20154.
  rewrite ?node_20158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20160 (s : N.State) (i : N.Inputs) :
  R.v20160 (state s) (inputs i) = Zmod.unsigned (N.v20160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20160 s i)) at 1.
  unfold R.v20160, N.v20160.
  unfold R.v6, N.v6.
  rewrite ?node_20159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20161 (s : N.State) (i : N.Inputs) :
  R.v20161 (state s) (inputs i) = Zmod.unsigned (N.v20161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20161 s i)) at 1.
  unfold R.v20161, N.v20161.
  rewrite ?node_6912.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20162 (s : N.State) (i : N.Inputs) :
  R.v20162 (state s) (inputs i) = Zmod.unsigned (N.v20162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20162 s i)) at 1.
  unfold R.v20162, N.v20162.
  unfold R.v6, N.v6.
  rewrite ?node_7032.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20163 (s : N.State) (i : N.Inputs) :
  R.v20163 (state s) (inputs i) = Zmod.unsigned (N.v20163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20163 s i)) at 1.
  unfold R.v20163, N.v20163.
  rewrite ?node_20161.
  rewrite ?node_20162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20164 (s : N.State) (i : N.Inputs) :
  R.v20164 (state s) (inputs i) = Zmod.unsigned (N.v20164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20164 s i)) at 1.
  unfold R.v20164, N.v20164.
  rewrite ?node_20160.
  rewrite ?node_20163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20165 (s : N.State) (i : N.Inputs) :
  R.v20165 (state s) (inputs i) = Zmod.unsigned (N.v20165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20165 s i)) at 1.
  unfold R.v20165, N.v20165.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20166 (s : N.State) (i : N.Inputs) :
  R.v20166 (state s) (inputs i) = Zmod.unsigned (N.v20166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20166 s i)) at 1.
  unfold R.v20166, N.v20166.
  rewrite ?node_6972.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20167 (s : N.State) (i : N.Inputs) :
  R.v20167 (state s) (inputs i) = Zmod.unsigned (N.v20167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20167 s i)) at 1.
  unfold R.v20167, N.v20167.
  unfold R.v16463, N.v16463.
  rewrite !state_r421_nr_5F421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r421_nr_5F421 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20168 (s : N.State) (i : N.Inputs) :
  R.v20168 (state s) (inputs i) = Zmod.unsigned (N.v20168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20168 s i)) at 1.
  unfold R.v20168, N.v20168.
  unfold R.v16463, N.v16463.
  rewrite !state_r420_nr_5F420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r420_nr_5F420 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20169 (s : N.State) (i : N.Inputs) :
  R.v20169 (state s) (inputs i) = Zmod.unsigned (N.v20169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20169 s i)) at 1.
  unfold R.v20169, N.v20169.
  unfold R.v6, N.v6.
  rewrite !state_r419_nr_5F419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r419_nr_5F419 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20170 (s : N.State) (i : N.Inputs) :
  R.v20170 (state s) (inputs i) = Zmod.unsigned (N.v20170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20170 s i)) at 1.
  unfold R.v20170, N.v20170.
  unfold R.v6, N.v6.
  rewrite !state_r418_nr_5F418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r418_nr_5F418 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20171 (s : N.State) (i : N.Inputs) :
  R.v20171 (state s) (inputs i) = Zmod.unsigned (N.v20171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20171 s i)) at 1.
  unfold R.v20171, N.v20171.
  rewrite ?node_20169.
  rewrite ?node_20170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20172 (s : N.State) (i : N.Inputs) :
  R.v20172 (state s) (inputs i) = Zmod.unsigned (N.v20172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20172 s i)) at 1.
  unfold R.v20172, N.v20172.
  unfold R.v16484, N.v16484.
  rewrite ?node_20171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20173 (s : N.State) (i : N.Inputs) :
  R.v20173 (state s) (inputs i) = Zmod.unsigned (N.v20173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20173 s i)) at 1.
  unfold R.v20173, N.v20173.
  rewrite ?node_20166.
  rewrite ?node_20167.
  rewrite ?node_20168.
  rewrite ?node_20172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20174 (s : N.State) (i : N.Inputs) :
  R.v20174 (state s) (inputs i) = Zmod.unsigned (N.v20174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20174 s i)) at 1.
  unfold R.v20174, N.v20174.
  unfold R.v6, N.v6.
  rewrite ?node_20173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20175 (s : N.State) (i : N.Inputs) :
  R.v20175 (state s) (inputs i) = Zmod.unsigned (N.v20175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20175 s i)) at 1.
  unfold R.v20175, N.v20175.
  rewrite ?node_6973.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20176 (s : N.State) (i : N.Inputs) :
  R.v20176 (state s) (inputs i) = Zmod.unsigned (N.v20176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20176 s i)) at 1.
  unfold R.v20176, N.v20176.
  unfold R.v6, N.v6.
  rewrite ?node_7071.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20177 (s : N.State) (i : N.Inputs) :
  R.v20177 (state s) (inputs i) = Zmod.unsigned (N.v20177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20177 s i)) at 1.
  unfold R.v20177, N.v20177.
  unfold R.v6, N.v6.
  rewrite ?node_7111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20178 (s : N.State) (i : N.Inputs) :
  R.v20178 (state s) (inputs i) = Zmod.unsigned (N.v20178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20178 s i)) at 1.
  unfold R.v20178, N.v20178.
  rewrite ?node_20175.
  rewrite ?node_20176.
  rewrite ?node_20177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20179 (s : N.State) (i : N.Inputs) :
  R.v20179 (state s) (inputs i) = Zmod.unsigned (N.v20179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20179 s i)) at 1.
  unfold R.v20179, N.v20179.
  rewrite ?node_20174.
  rewrite ?node_20178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20180 (s : N.State) (i : N.Inputs) :
  R.v20180 (state s) (inputs i) = Zmod.unsigned (N.v20180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20180 s i)) at 1.
  unfold R.v20180, N.v20180.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20181 (s : N.State) (i : N.Inputs) :
  R.v20181 (state s) (inputs i) = Zmod.unsigned (N.v20181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20181 s i)) at 1.
  unfold R.v20181, N.v20181.
  unfold R.v16463, N.v16463.
  rewrite !state_r420_nr_5F420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r420_nr_5F420 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20182 (s : N.State) (i : N.Inputs) :
  R.v20182 (state s) (inputs i) = Zmod.unsigned (N.v20182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20182 s i)) at 1.
  unfold R.v20182, N.v20182.
  unfold R.v6, N.v6.
  rewrite !state_r419_nr_5F419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r419_nr_5F419 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20183 (s : N.State) (i : N.Inputs) :
  R.v20183 (state s) (inputs i) = Zmod.unsigned (N.v20183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20183 s i)) at 1.
  unfold R.v20183, N.v20183.
  unfold R.v6, N.v6.
  rewrite !state_r418_nr_5F418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r418_nr_5F418 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20184 (s : N.State) (i : N.Inputs) :
  R.v20184 (state s) (inputs i) = Zmod.unsigned (N.v20184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20184 s i)) at 1.
  unfold R.v20184, N.v20184.
  rewrite ?node_20182.
  rewrite ?node_20183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20185 (s : N.State) (i : N.Inputs) :
  R.v20185 (state s) (inputs i) = Zmod.unsigned (N.v20185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20185 s i)) at 1.
  unfold R.v20185, N.v20185.
  unfold R.v16484, N.v16484.
  rewrite ?node_20184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20186 (s : N.State) (i : N.Inputs) :
  R.v20186 (state s) (inputs i) = Zmod.unsigned (N.v20186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20186 s i)) at 1.
  unfold R.v20186, N.v20186.
  rewrite ?node_20181.
  rewrite ?node_20185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20187 (s : N.State) (i : N.Inputs) :
  R.v20187 (state s) (inputs i) = Zmod.unsigned (N.v20187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20187 s i)) at 1.
  unfold R.v20187, N.v20187.
  unfold R.v6, N.v6.
  rewrite ?node_20186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20188 (s : N.State) (i : N.Inputs) :
  R.v20188 (state s) (inputs i) = Zmod.unsigned (N.v20188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20188 s i)) at 1.
  unfold R.v20188, N.v20188.
  rewrite ?node_6968.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20189 (s : N.State) (i : N.Inputs) :
  R.v20189 (state s) (inputs i) = Zmod.unsigned (N.v20189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20189 s i)) at 1.
  unfold R.v20189, N.v20189.
  unfold R.v6, N.v6.
  rewrite ?node_7071.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20190 (s : N.State) (i : N.Inputs) :
  R.v20190 (state s) (inputs i) = Zmod.unsigned (N.v20190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20190 s i)) at 1.
  unfold R.v20190, N.v20190.
  rewrite ?node_20188.
  rewrite ?node_20189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20191 (s : N.State) (i : N.Inputs) :
  R.v20191 (state s) (inputs i) = Zmod.unsigned (N.v20191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20191 s i)) at 1.
  unfold R.v20191, N.v20191.
  rewrite ?node_20187.
  rewrite ?node_20190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20192 (s : N.State) (i : N.Inputs) :
  R.v20192 (state s) (inputs i) = Zmod.unsigned (N.v20192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20192 s i)) at 1.
  unfold R.v20192, N.v20192.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20193 (s : N.State) (i : N.Inputs) :
  R.v20193 (state s) (inputs i) = Zmod.unsigned (N.v20193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20193 s i)) at 1.
  unfold R.v20193, N.v20193.
  rewrite ?node_6972.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20194 (s : N.State) (i : N.Inputs) :
  R.v20194 (state s) (inputs i) = Zmod.unsigned (N.v20194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20194 s i)) at 1.
  unfold R.v20194, N.v20194.
  unfold R.v6, N.v6.
  rewrite !state_r421_nr_5F421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r421_nr_5F421 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20195 (s : N.State) (i : N.Inputs) :
  R.v20195 (state s) (inputs i) = Zmod.unsigned (N.v20195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20195 s i)) at 1.
  unfold R.v20195, N.v20195.
  unfold R.v6, N.v6.
  rewrite ?node_6968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20196 (s : N.State) (i : N.Inputs) :
  R.v20196 (state s) (inputs i) = Zmod.unsigned (N.v20196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20196 s i)) at 1.
  unfold R.v20196, N.v20196.
  rewrite ?node_20194.
  rewrite ?node_20195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20197 (s : N.State) (i : N.Inputs) :
  R.v20197 (state s) (inputs i) = Zmod.unsigned (N.v20197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20197 s i)) at 1.
  unfold R.v20197, N.v20197.
  unfold R.v16484, N.v16484.
  rewrite ?node_20196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20198 (s : N.State) (i : N.Inputs) :
  R.v20198 (state s) (inputs i) = Zmod.unsigned (N.v20198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20198 s i)) at 1.
  unfold R.v20198, N.v20198.
  rewrite ?node_20193.
  rewrite ?node_20197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20199 (s : N.State) (i : N.Inputs) :
  R.v20199 (state s) (inputs i) = Zmod.unsigned (N.v20199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20199 s i)) at 1.
  unfold R.v20199, N.v20199.
  unfold R.v6, N.v6.
  rewrite ?node_20198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20200 (s : N.State) (i : N.Inputs) :
  R.v20200 (state s) (inputs i) = Zmod.unsigned (N.v20200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20200 s i)) at 1.
  unfold R.v20200, N.v20200.
  rewrite ?node_6973.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20201 (s : N.State) (i : N.Inputs) :
  R.v20201 (state s) (inputs i) = Zmod.unsigned (N.v20201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20201 s i)) at 1.
  unfold R.v20201, N.v20201.
  unfold R.v6, N.v6.
  rewrite ?node_7111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20202 (s : N.State) (i : N.Inputs) :
  R.v20202 (state s) (inputs i) = Zmod.unsigned (N.v20202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20202 s i)) at 1.
  unfold R.v20202, N.v20202.
  rewrite ?node_20200.
  rewrite ?node_20201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20203 (s : N.State) (i : N.Inputs) :
  R.v20203 (state s) (inputs i) = Zmod.unsigned (N.v20203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20203 s i)) at 1.
  unfold R.v20203, N.v20203.
  rewrite ?node_20199.
  rewrite ?node_20202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20204 (s : N.State) (i : N.Inputs) :
  R.v20204 (state s) (inputs i) = Zmod.unsigned (N.v20204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20204 s i)) at 1.
  unfold R.v20204, N.v20204.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20205 (s : N.State) (i : N.Inputs) :
  R.v20205 (state s) (inputs i) = Zmod.unsigned (N.v20205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20205 s i)) at 1.
  unfold R.v20205, N.v20205.
  rewrite ?node_6979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20206 (s : N.State) (i : N.Inputs) :
  R.v20206 (state s) (inputs i) = Zmod.unsigned (N.v20206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20206 s i)) at 1.
  unfold R.v20206, N.v20206.
  unfold R.v16463, N.v16463.
  rewrite !state_r425_nr_5F425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r425_nr_5F425 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20207 (s : N.State) (i : N.Inputs) :
  R.v20207 (state s) (inputs i) = Zmod.unsigned (N.v20207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20207 s i)) at 1.
  unfold R.v20207, N.v20207.
  unfold R.v16463, N.v16463.
  rewrite !state_r424_nr_5F424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r424_nr_5F424 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20208 (s : N.State) (i : N.Inputs) :
  R.v20208 (state s) (inputs i) = Zmod.unsigned (N.v20208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20208 s i)) at 1.
  unfold R.v20208, N.v20208.
  unfold R.v6, N.v6.
  rewrite !state_r423_nr_5F423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r423_nr_5F423 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20209 (s : N.State) (i : N.Inputs) :
  R.v20209 (state s) (inputs i) = Zmod.unsigned (N.v20209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20209 s i)) at 1.
  unfold R.v20209, N.v20209.
  unfold R.v6, N.v6.
  rewrite !state_r422_nr_5F422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r422_nr_5F422 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20210 (s : N.State) (i : N.Inputs) :
  R.v20210 (state s) (inputs i) = Zmod.unsigned (N.v20210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20210 s i)) at 1.
  unfold R.v20210, N.v20210.
  rewrite ?node_20208.
  rewrite ?node_20209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20211 (s : N.State) (i : N.Inputs) :
  R.v20211 (state s) (inputs i) = Zmod.unsigned (N.v20211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20211 s i)) at 1.
  unfold R.v20211, N.v20211.
  unfold R.v16484, N.v16484.
  rewrite ?node_20210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20212 (s : N.State) (i : N.Inputs) :
  R.v20212 (state s) (inputs i) = Zmod.unsigned (N.v20212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20212 s i)) at 1.
  unfold R.v20212, N.v20212.
  rewrite ?node_20205.
  rewrite ?node_20206.
  rewrite ?node_20207.
  rewrite ?node_20211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20213 (s : N.State) (i : N.Inputs) :
  R.v20213 (state s) (inputs i) = Zmod.unsigned (N.v20213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20213 s i)) at 1.
  unfold R.v20213, N.v20213.
  unfold R.v6, N.v6.
  rewrite ?node_20212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20214 (s : N.State) (i : N.Inputs) :
  R.v20214 (state s) (inputs i) = Zmod.unsigned (N.v20214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20214 s i)) at 1.
  unfold R.v20214, N.v20214.
  rewrite ?node_6980.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20215 (s : N.State) (i : N.Inputs) :
  R.v20215 (state s) (inputs i) = Zmod.unsigned (N.v20215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20215 s i)) at 1.
  unfold R.v20215, N.v20215.
  unfold R.v6, N.v6.
  rewrite ?node_7078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20216 (s : N.State) (i : N.Inputs) :
  R.v20216 (state s) (inputs i) = Zmod.unsigned (N.v20216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20216 s i)) at 1.
  unfold R.v20216, N.v20216.
  unfold R.v6, N.v6.
  rewrite ?node_7115.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20217 (s : N.State) (i : N.Inputs) :
  R.v20217 (state s) (inputs i) = Zmod.unsigned (N.v20217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20217 s i)) at 1.
  unfold R.v20217, N.v20217.
  rewrite ?node_20214.
  rewrite ?node_20215.
  rewrite ?node_20216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20218 (s : N.State) (i : N.Inputs) :
  R.v20218 (state s) (inputs i) = Zmod.unsigned (N.v20218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20218 s i)) at 1.
  unfold R.v20218, N.v20218.
  rewrite ?node_20213.
  rewrite ?node_20217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20219 (s : N.State) (i : N.Inputs) :
  R.v20219 (state s) (inputs i) = Zmod.unsigned (N.v20219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20219 s i)) at 1.
  unfold R.v20219, N.v20219.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20220 (s : N.State) (i : N.Inputs) :
  R.v20220 (state s) (inputs i) = Zmod.unsigned (N.v20220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20220 s i)) at 1.
  unfold R.v20220, N.v20220.
  unfold R.v16463, N.v16463.
  rewrite !state_r424_nr_5F424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r424_nr_5F424 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20221 (s : N.State) (i : N.Inputs) :
  R.v20221 (state s) (inputs i) = Zmod.unsigned (N.v20221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20221 s i)) at 1.
  unfold R.v20221, N.v20221.
  unfold R.v6, N.v6.
  rewrite !state_r423_nr_5F423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r423_nr_5F423 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20222 (s : N.State) (i : N.Inputs) :
  R.v20222 (state s) (inputs i) = Zmod.unsigned (N.v20222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20222 s i)) at 1.
  unfold R.v20222, N.v20222.
  unfold R.v6, N.v6.
  rewrite !state_r422_nr_5F422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r422_nr_5F422 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20223 (s : N.State) (i : N.Inputs) :
  R.v20223 (state s) (inputs i) = Zmod.unsigned (N.v20223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20223 s i)) at 1.
  unfold R.v20223, N.v20223.
  rewrite ?node_20221.
  rewrite ?node_20222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20224 (s : N.State) (i : N.Inputs) :
  R.v20224 (state s) (inputs i) = Zmod.unsigned (N.v20224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20224 s i)) at 1.
  unfold R.v20224, N.v20224.
  unfold R.v16484, N.v16484.
  rewrite ?node_20223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20225 (s : N.State) (i : N.Inputs) :
  R.v20225 (state s) (inputs i) = Zmod.unsigned (N.v20225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20225 s i)) at 1.
  unfold R.v20225, N.v20225.
  rewrite ?node_20220.
  rewrite ?node_20224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20226 (s : N.State) (i : N.Inputs) :
  R.v20226 (state s) (inputs i) = Zmod.unsigned (N.v20226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20226 s i)) at 1.
  unfold R.v20226, N.v20226.
  unfold R.v6, N.v6.
  rewrite ?node_20225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20227 (s : N.State) (i : N.Inputs) :
  R.v20227 (state s) (inputs i) = Zmod.unsigned (N.v20227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20227 s i)) at 1.
  unfold R.v20227, N.v20227.
  rewrite ?node_6975.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20228 (s : N.State) (i : N.Inputs) :
  R.v20228 (state s) (inputs i) = Zmod.unsigned (N.v20228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20228 s i)) at 1.
  unfold R.v20228, N.v20228.
  unfold R.v6, N.v6.
  rewrite ?node_7078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20229 (s : N.State) (i : N.Inputs) :
  R.v20229 (state s) (inputs i) = Zmod.unsigned (N.v20229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20229 s i)) at 1.
  unfold R.v20229, N.v20229.
  rewrite ?node_20227.
  rewrite ?node_20228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20230 (s : N.State) (i : N.Inputs) :
  R.v20230 (state s) (inputs i) = Zmod.unsigned (N.v20230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20230 s i)) at 1.
  unfold R.v20230, N.v20230.
  rewrite ?node_20226.
  rewrite ?node_20229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20231 (s : N.State) (i : N.Inputs) :
  R.v20231 (state s) (inputs i) = Zmod.unsigned (N.v20231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20231 s i)) at 1.
  unfold R.v20231, N.v20231.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20232 (s : N.State) (i : N.Inputs) :
  R.v20232 (state s) (inputs i) = Zmod.unsigned (N.v20232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20232 s i)) at 1.
  unfold R.v20232, N.v20232.
  rewrite ?node_6979.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20233 (s : N.State) (i : N.Inputs) :
  R.v20233 (state s) (inputs i) = Zmod.unsigned (N.v20233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20233 s i)) at 1.
  unfold R.v20233, N.v20233.
  unfold R.v6, N.v6.
  rewrite !state_r425_nr_5F425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r425_nr_5F425 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20234 (s : N.State) (i : N.Inputs) :
  R.v20234 (state s) (inputs i) = Zmod.unsigned (N.v20234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20234 s i)) at 1.
  unfold R.v20234, N.v20234.
  unfold R.v6, N.v6.
  rewrite ?node_6975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20235 (s : N.State) (i : N.Inputs) :
  R.v20235 (state s) (inputs i) = Zmod.unsigned (N.v20235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20235 s i)) at 1.
  unfold R.v20235, N.v20235.
  rewrite ?node_20233.
  rewrite ?node_20234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20236 (s : N.State) (i : N.Inputs) :
  R.v20236 (state s) (inputs i) = Zmod.unsigned (N.v20236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20236 s i)) at 1.
  unfold R.v20236, N.v20236.
  unfold R.v16484, N.v16484.
  rewrite ?node_20235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20237 (s : N.State) (i : N.Inputs) :
  R.v20237 (state s) (inputs i) = Zmod.unsigned (N.v20237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20237 s i)) at 1.
  unfold R.v20237, N.v20237.
  rewrite ?node_20232.
  rewrite ?node_20236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20238 (s : N.State) (i : N.Inputs) :
  R.v20238 (state s) (inputs i) = Zmod.unsigned (N.v20238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20238 s i)) at 1.
  unfold R.v20238, N.v20238.
  unfold R.v6, N.v6.
  rewrite ?node_20237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20239 (s : N.State) (i : N.Inputs) :
  R.v20239 (state s) (inputs i) = Zmod.unsigned (N.v20239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20239 s i)) at 1.
  unfold R.v20239, N.v20239.
  rewrite ?node_6980.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20240 (s : N.State) (i : N.Inputs) :
  R.v20240 (state s) (inputs i) = Zmod.unsigned (N.v20240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20240 s i)) at 1.
  unfold R.v20240, N.v20240.
  unfold R.v6, N.v6.
  rewrite ?node_7115.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20241 (s : N.State) (i : N.Inputs) :
  R.v20241 (state s) (inputs i) = Zmod.unsigned (N.v20241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20241 s i)) at 1.
  unfold R.v20241, N.v20241.
  rewrite ?node_20239.
  rewrite ?node_20240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20242 (s : N.State) (i : N.Inputs) :
  R.v20242 (state s) (inputs i) = Zmod.unsigned (N.v20242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20242 s i)) at 1.
  unfold R.v20242, N.v20242.
  rewrite ?node_20238.
  rewrite ?node_20241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20243 (s : N.State) (i : N.Inputs) :
  R.v20243 (state s) (inputs i) = Zmod.unsigned (N.v20243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20243 s i)) at 1.
  unfold R.v20243, N.v20243.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20244 (s : N.State) (i : N.Inputs) :
  R.v20244 (state s) (inputs i) = Zmod.unsigned (N.v20244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20244 s i)) at 1.
  unfold R.v20244, N.v20244.
  rewrite ?node_6987.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20245 (s : N.State) (i : N.Inputs) :
  R.v20245 (state s) (inputs i) = Zmod.unsigned (N.v20245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20245 s i)) at 1.
  unfold R.v20245, N.v20245.
  unfold R.v16463, N.v16463.
  rewrite !state_r429_nr_5F429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r429_nr_5F429 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20246 (s : N.State) (i : N.Inputs) :
  R.v20246 (state s) (inputs i) = Zmod.unsigned (N.v20246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20246 s i)) at 1.
  unfold R.v20246, N.v20246.
  unfold R.v16463, N.v16463.
  rewrite !state_r428_nr_5F428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r428_nr_5F428 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20247 (s : N.State) (i : N.Inputs) :
  R.v20247 (state s) (inputs i) = Zmod.unsigned (N.v20247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20247 s i)) at 1.
  unfold R.v20247, N.v20247.
  unfold R.v6, N.v6.
  rewrite !state_r427_nr_5F427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r427_nr_5F427 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20248 (s : N.State) (i : N.Inputs) :
  R.v20248 (state s) (inputs i) = Zmod.unsigned (N.v20248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20248 s i)) at 1.
  unfold R.v20248, N.v20248.
  unfold R.v6, N.v6.
  rewrite !state_r426_nr_5F426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r426_nr_5F426 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20249 (s : N.State) (i : N.Inputs) :
  R.v20249 (state s) (inputs i) = Zmod.unsigned (N.v20249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20249 s i)) at 1.
  unfold R.v20249, N.v20249.
  rewrite ?node_20247.
  rewrite ?node_20248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20250 (s : N.State) (i : N.Inputs) :
  R.v20250 (state s) (inputs i) = Zmod.unsigned (N.v20250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20250 s i)) at 1.
  unfold R.v20250, N.v20250.
  unfold R.v16484, N.v16484.
  rewrite ?node_20249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20251 (s : N.State) (i : N.Inputs) :
  R.v20251 (state s) (inputs i) = Zmod.unsigned (N.v20251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20251 s i)) at 1.
  unfold R.v20251, N.v20251.
  rewrite ?node_20244.
  rewrite ?node_20245.
  rewrite ?node_20246.
  rewrite ?node_20250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20252 (s : N.State) (i : N.Inputs) :
  R.v20252 (state s) (inputs i) = Zmod.unsigned (N.v20252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20252 s i)) at 1.
  unfold R.v20252, N.v20252.
  unfold R.v6, N.v6.
  rewrite ?node_20251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20253 (s : N.State) (i : N.Inputs) :
  R.v20253 (state s) (inputs i) = Zmod.unsigned (N.v20253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20253 s i)) at 1.
  unfold R.v20253, N.v20253.
  rewrite ?node_6988.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20254 (s : N.State) (i : N.Inputs) :
  R.v20254 (state s) (inputs i) = Zmod.unsigned (N.v20254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20254 s i)) at 1.
  unfold R.v20254, N.v20254.
  unfold R.v6, N.v6.
  rewrite ?node_7086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20255 (s : N.State) (i : N.Inputs) :
  R.v20255 (state s) (inputs i) = Zmod.unsigned (N.v20255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20255 s i)) at 1.
  unfold R.v20255, N.v20255.
  unfold R.v6, N.v6.
  rewrite ?node_7124.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20256 (s : N.State) (i : N.Inputs) :
  R.v20256 (state s) (inputs i) = Zmod.unsigned (N.v20256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20256 s i)) at 1.
  unfold R.v20256, N.v20256.
  rewrite ?node_20253.
  rewrite ?node_20254.
  rewrite ?node_20255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20257 (s : N.State) (i : N.Inputs) :
  R.v20257 (state s) (inputs i) = Zmod.unsigned (N.v20257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20257 s i)) at 1.
  unfold R.v20257, N.v20257.
  rewrite ?node_20252.
  rewrite ?node_20256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20258 (s : N.State) (i : N.Inputs) :
  R.v20258 (state s) (inputs i) = Zmod.unsigned (N.v20258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20258 s i)) at 1.
  unfold R.v20258, N.v20258.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20259 (s : N.State) (i : N.Inputs) :
  R.v20259 (state s) (inputs i) = Zmod.unsigned (N.v20259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20259 s i)) at 1.
  unfold R.v20259, N.v20259.
  unfold R.v16463, N.v16463.
  rewrite !state_r428_nr_5F428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r428_nr_5F428 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20260 (s : N.State) (i : N.Inputs) :
  R.v20260 (state s) (inputs i) = Zmod.unsigned (N.v20260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20260 s i)) at 1.
  unfold R.v20260, N.v20260.
  unfold R.v6, N.v6.
  rewrite !state_r427_nr_5F427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r427_nr_5F427 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20261 (s : N.State) (i : N.Inputs) :
  R.v20261 (state s) (inputs i) = Zmod.unsigned (N.v20261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20261 s i)) at 1.
  unfold R.v20261, N.v20261.
  unfold R.v6, N.v6.
  rewrite !state_r426_nr_5F426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r426_nr_5F426 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20262 (s : N.State) (i : N.Inputs) :
  R.v20262 (state s) (inputs i) = Zmod.unsigned (N.v20262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20262 s i)) at 1.
  unfold R.v20262, N.v20262.
  rewrite ?node_20260.
  rewrite ?node_20261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20263 (s : N.State) (i : N.Inputs) :
  R.v20263 (state s) (inputs i) = Zmod.unsigned (N.v20263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20263 s i)) at 1.
  unfold R.v20263, N.v20263.
  unfold R.v16484, N.v16484.
  rewrite ?node_20262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20264 (s : N.State) (i : N.Inputs) :
  R.v20264 (state s) (inputs i) = Zmod.unsigned (N.v20264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20264 s i)) at 1.
  unfold R.v20264, N.v20264.
  rewrite ?node_20259.
  rewrite ?node_20263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20265 (s : N.State) (i : N.Inputs) :
  R.v20265 (state s) (inputs i) = Zmod.unsigned (N.v20265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20265 s i)) at 1.
  unfold R.v20265, N.v20265.
  unfold R.v6, N.v6.
  rewrite ?node_20264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20266 (s : N.State) (i : N.Inputs) :
  R.v20266 (state s) (inputs i) = Zmod.unsigned (N.v20266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20266 s i)) at 1.
  unfold R.v20266, N.v20266.
  rewrite ?node_6983.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20267 (s : N.State) (i : N.Inputs) :
  R.v20267 (state s) (inputs i) = Zmod.unsigned (N.v20267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20267 s i)) at 1.
  unfold R.v20267, N.v20267.
  unfold R.v6, N.v6.
  rewrite ?node_7086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20268 (s : N.State) (i : N.Inputs) :
  R.v20268 (state s) (inputs i) = Zmod.unsigned (N.v20268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20268 s i)) at 1.
  unfold R.v20268, N.v20268.
  rewrite ?node_20266.
  rewrite ?node_20267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20269 (s : N.State) (i : N.Inputs) :
  R.v20269 (state s) (inputs i) = Zmod.unsigned (N.v20269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20269 s i)) at 1.
  unfold R.v20269, N.v20269.
  rewrite ?node_20265.
  rewrite ?node_20268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20270 (s : N.State) (i : N.Inputs) :
  R.v20270 (state s) (inputs i) = Zmod.unsigned (N.v20270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20270 s i)) at 1.
  unfold R.v20270, N.v20270.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20271 (s : N.State) (i : N.Inputs) :
  R.v20271 (state s) (inputs i) = Zmod.unsigned (N.v20271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20271 s i)) at 1.
  unfold R.v20271, N.v20271.
  rewrite ?node_6987.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20272 (s : N.State) (i : N.Inputs) :
  R.v20272 (state s) (inputs i) = Zmod.unsigned (N.v20272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20272 s i)) at 1.
  unfold R.v20272, N.v20272.
  unfold R.v6, N.v6.
  rewrite !state_r429_nr_5F429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r429_nr_5F429 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20273 (s : N.State) (i : N.Inputs) :
  R.v20273 (state s) (inputs i) = Zmod.unsigned (N.v20273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20273 s i)) at 1.
  unfold R.v20273, N.v20273.
  unfold R.v6, N.v6.
  rewrite ?node_6983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20274 (s : N.State) (i : N.Inputs) :
  R.v20274 (state s) (inputs i) = Zmod.unsigned (N.v20274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20274 s i)) at 1.
  unfold R.v20274, N.v20274.
  rewrite ?node_20272.
  rewrite ?node_20273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20275 (s : N.State) (i : N.Inputs) :
  R.v20275 (state s) (inputs i) = Zmod.unsigned (N.v20275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20275 s i)) at 1.
  unfold R.v20275, N.v20275.
  unfold R.v16484, N.v16484.
  rewrite ?node_20274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20276 (s : N.State) (i : N.Inputs) :
  R.v20276 (state s) (inputs i) = Zmod.unsigned (N.v20276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20276 s i)) at 1.
  unfold R.v20276, N.v20276.
  rewrite ?node_20271.
  rewrite ?node_20275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20277 (s : N.State) (i : N.Inputs) :
  R.v20277 (state s) (inputs i) = Zmod.unsigned (N.v20277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20277 s i)) at 1.
  unfold R.v20277, N.v20277.
  unfold R.v6, N.v6.
  rewrite ?node_20276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20278 (s : N.State) (i : N.Inputs) :
  R.v20278 (state s) (inputs i) = Zmod.unsigned (N.v20278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20278 s i)) at 1.
  unfold R.v20278, N.v20278.
  rewrite ?node_6988.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20279 (s : N.State) (i : N.Inputs) :
  R.v20279 (state s) (inputs i) = Zmod.unsigned (N.v20279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20279 s i)) at 1.
  unfold R.v20279, N.v20279.
  unfold R.v6, N.v6.
  rewrite ?node_7124.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20280 (s : N.State) (i : N.Inputs) :
  R.v20280 (state s) (inputs i) = Zmod.unsigned (N.v20280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20280 s i)) at 1.
  unfold R.v20280, N.v20280.
  rewrite ?node_20278.
  rewrite ?node_20279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20281 (s : N.State) (i : N.Inputs) :
  R.v20281 (state s) (inputs i) = Zmod.unsigned (N.v20281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20281 s i)) at 1.
  unfold R.v20281, N.v20281.
  rewrite ?node_20277.
  rewrite ?node_20280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20282 (s : N.State) (i : N.Inputs) :
  R.v20282 (state s) (inputs i) = Zmod.unsigned (N.v20282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20282 s i)) at 1.
  unfold R.v20282, N.v20282.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20283 (s : N.State) (i : N.Inputs) :
  R.v20283 (state s) (inputs i) = Zmod.unsigned (N.v20283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20283 s i)) at 1.
  unfold R.v20283, N.v20283.
  rewrite ?node_6995.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20284 (s : N.State) (i : N.Inputs) :
  R.v20284 (state s) (inputs i) = Zmod.unsigned (N.v20284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20284 s i)) at 1.
  unfold R.v20284, N.v20284.
  unfold R.v16463, N.v16463.
  rewrite !state_r433_nr_5F433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r433_nr_5F433 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20285 (s : N.State) (i : N.Inputs) :
  R.v20285 (state s) (inputs i) = Zmod.unsigned (N.v20285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20285 s i)) at 1.
  unfold R.v20285, N.v20285.
  unfold R.v16463, N.v16463.
  rewrite !state_r432_nr_5F432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r432_nr_5F432 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20286 (s : N.State) (i : N.Inputs) :
  R.v20286 (state s) (inputs i) = Zmod.unsigned (N.v20286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20286 s i)) at 1.
  unfold R.v20286, N.v20286.
  unfold R.v6, N.v6.
  rewrite !state_r431_nr_5F431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r431_nr_5F431 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20287 (s : N.State) (i : N.Inputs) :
  R.v20287 (state s) (inputs i) = Zmod.unsigned (N.v20287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20287 s i)) at 1.
  unfold R.v20287, N.v20287.
  unfold R.v6, N.v6.
  rewrite !state_r430_nr_5F430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r430_nr_5F430 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20288 (s : N.State) (i : N.Inputs) :
  R.v20288 (state s) (inputs i) = Zmod.unsigned (N.v20288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20288 s i)) at 1.
  unfold R.v20288, N.v20288.
  rewrite ?node_20286.
  rewrite ?node_20287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20289 (s : N.State) (i : N.Inputs) :
  R.v20289 (state s) (inputs i) = Zmod.unsigned (N.v20289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20289 s i)) at 1.
  unfold R.v20289, N.v20289.
  unfold R.v16484, N.v16484.
  rewrite ?node_20288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20290 (s : N.State) (i : N.Inputs) :
  R.v20290 (state s) (inputs i) = Zmod.unsigned (N.v20290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20290 s i)) at 1.
  unfold R.v20290, N.v20290.
  rewrite ?node_20283.
  rewrite ?node_20284.
  rewrite ?node_20285.
  rewrite ?node_20289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20291 (s : N.State) (i : N.Inputs) :
  R.v20291 (state s) (inputs i) = Zmod.unsigned (N.v20291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20291 s i)) at 1.
  unfold R.v20291, N.v20291.
  unfold R.v6, N.v6.
  rewrite ?node_20290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20292 (s : N.State) (i : N.Inputs) :
  R.v20292 (state s) (inputs i) = Zmod.unsigned (N.v20292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20292 s i)) at 1.
  unfold R.v20292, N.v20292.
  rewrite ?node_6996.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20293 (s : N.State) (i : N.Inputs) :
  R.v20293 (state s) (inputs i) = Zmod.unsigned (N.v20293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20293 s i)) at 1.
  unfold R.v20293, N.v20293.
  unfold R.v6, N.v6.
  rewrite ?node_7094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20294 (s : N.State) (i : N.Inputs) :
  R.v20294 (state s) (inputs i) = Zmod.unsigned (N.v20294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20294 s i)) at 1.
  unfold R.v20294, N.v20294.
  unfold R.v6, N.v6.
  rewrite ?node_7127.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20295 (s : N.State) (i : N.Inputs) :
  R.v20295 (state s) (inputs i) = Zmod.unsigned (N.v20295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20295 s i)) at 1.
  unfold R.v20295, N.v20295.
  rewrite ?node_20292.
  rewrite ?node_20293.
  rewrite ?node_20294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20296 (s : N.State) (i : N.Inputs) :
  R.v20296 (state s) (inputs i) = Zmod.unsigned (N.v20296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20296 s i)) at 1.
  unfold R.v20296, N.v20296.
  rewrite ?node_20291.
  rewrite ?node_20295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20297 (s : N.State) (i : N.Inputs) :
  R.v20297 (state s) (inputs i) = Zmod.unsigned (N.v20297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20297 s i)) at 1.
  unfold R.v20297, N.v20297.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20298 (s : N.State) (i : N.Inputs) :
  R.v20298 (state s) (inputs i) = Zmod.unsigned (N.v20298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20298 s i)) at 1.
  unfold R.v20298, N.v20298.
  unfold R.v16463, N.v16463.
  rewrite !state_r432_nr_5F432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r432_nr_5F432 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20299 (s : N.State) (i : N.Inputs) :
  R.v20299 (state s) (inputs i) = Zmod.unsigned (N.v20299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20299 s i)) at 1.
  unfold R.v20299, N.v20299.
  unfold R.v6, N.v6.
  rewrite !state_r431_nr_5F431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r431_nr_5F431 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20300 (s : N.State) (i : N.Inputs) :
  R.v20300 (state s) (inputs i) = Zmod.unsigned (N.v20300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20300 s i)) at 1.
  unfold R.v20300, N.v20300.
  unfold R.v6, N.v6.
  rewrite !state_r430_nr_5F430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r430_nr_5F430 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20301 (s : N.State) (i : N.Inputs) :
  R.v20301 (state s) (inputs i) = Zmod.unsigned (N.v20301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20301 s i)) at 1.
  unfold R.v20301, N.v20301.
  rewrite ?node_20299.
  rewrite ?node_20300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20302 (s : N.State) (i : N.Inputs) :
  R.v20302 (state s) (inputs i) = Zmod.unsigned (N.v20302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20302 s i)) at 1.
  unfold R.v20302, N.v20302.
  unfold R.v16484, N.v16484.
  rewrite ?node_20301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20303 (s : N.State) (i : N.Inputs) :
  R.v20303 (state s) (inputs i) = Zmod.unsigned (N.v20303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20303 s i)) at 1.
  unfold R.v20303, N.v20303.
  rewrite ?node_20298.
  rewrite ?node_20302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20304 (s : N.State) (i : N.Inputs) :
  R.v20304 (state s) (inputs i) = Zmod.unsigned (N.v20304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20304 s i)) at 1.
  unfold R.v20304, N.v20304.
  unfold R.v6, N.v6.
  rewrite ?node_20303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20305 (s : N.State) (i : N.Inputs) :
  R.v20305 (state s) (inputs i) = Zmod.unsigned (N.v20305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20305 s i)) at 1.
  unfold R.v20305, N.v20305.
  rewrite ?node_6991.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20306 (s : N.State) (i : N.Inputs) :
  R.v20306 (state s) (inputs i) = Zmod.unsigned (N.v20306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20306 s i)) at 1.
  unfold R.v20306, N.v20306.
  unfold R.v6, N.v6.
  rewrite ?node_7094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20307 (s : N.State) (i : N.Inputs) :
  R.v20307 (state s) (inputs i) = Zmod.unsigned (N.v20307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20307 s i)) at 1.
  unfold R.v20307, N.v20307.
  rewrite ?node_20305.
  rewrite ?node_20306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20308 (s : N.State) (i : N.Inputs) :
  R.v20308 (state s) (inputs i) = Zmod.unsigned (N.v20308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20308 s i)) at 1.
  unfold R.v20308, N.v20308.
  rewrite ?node_20304.
  rewrite ?node_20307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20309 (s : N.State) (i : N.Inputs) :
  R.v20309 (state s) (inputs i) = Zmod.unsigned (N.v20309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20309 s i)) at 1.
  unfold R.v20309, N.v20309.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20310 (s : N.State) (i : N.Inputs) :
  R.v20310 (state s) (inputs i) = Zmod.unsigned (N.v20310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20310 s i)) at 1.
  unfold R.v20310, N.v20310.
  rewrite ?node_6995.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20311 (s : N.State) (i : N.Inputs) :
  R.v20311 (state s) (inputs i) = Zmod.unsigned (N.v20311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20311 s i)) at 1.
  unfold R.v20311, N.v20311.
  unfold R.v6, N.v6.
  rewrite !state_r433_nr_5F433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r433_nr_5F433 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20312 (s : N.State) (i : N.Inputs) :
  R.v20312 (state s) (inputs i) = Zmod.unsigned (N.v20312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20312 s i)) at 1.
  unfold R.v20312, N.v20312.
  unfold R.v6, N.v6.
  rewrite ?node_6991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20313 (s : N.State) (i : N.Inputs) :
  R.v20313 (state s) (inputs i) = Zmod.unsigned (N.v20313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20313 s i)) at 1.
  unfold R.v20313, N.v20313.
  rewrite ?node_20311.
  rewrite ?node_20312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20314 (s : N.State) (i : N.Inputs) :
  R.v20314 (state s) (inputs i) = Zmod.unsigned (N.v20314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20314 s i)) at 1.
  unfold R.v20314, N.v20314.
  unfold R.v16484, N.v16484.
  rewrite ?node_20313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20315 (s : N.State) (i : N.Inputs) :
  R.v20315 (state s) (inputs i) = Zmod.unsigned (N.v20315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20315 s i)) at 1.
  unfold R.v20315, N.v20315.
  rewrite ?node_20310.
  rewrite ?node_20314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20316 (s : N.State) (i : N.Inputs) :
  R.v20316 (state s) (inputs i) = Zmod.unsigned (N.v20316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20316 s i)) at 1.
  unfold R.v20316, N.v20316.
  unfold R.v6, N.v6.
  rewrite ?node_20315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20317 (s : N.State) (i : N.Inputs) :
  R.v20317 (state s) (inputs i) = Zmod.unsigned (N.v20317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20317 s i)) at 1.
  unfold R.v20317, N.v20317.
  rewrite ?node_6996.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20318 (s : N.State) (i : N.Inputs) :
  R.v20318 (state s) (inputs i) = Zmod.unsigned (N.v20318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20318 s i)) at 1.
  unfold R.v20318, N.v20318.
  unfold R.v6, N.v6.
  rewrite ?node_7127.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20319 (s : N.State) (i : N.Inputs) :
  R.v20319 (state s) (inputs i) = Zmod.unsigned (N.v20319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20319 s i)) at 1.
  unfold R.v20319, N.v20319.
  rewrite ?node_20317.
  rewrite ?node_20318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20320 (s : N.State) (i : N.Inputs) :
  R.v20320 (state s) (inputs i) = Zmod.unsigned (N.v20320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20320 s i)) at 1.
  unfold R.v20320, N.v20320.
  rewrite ?node_20316.
  rewrite ?node_20319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20321 (s : N.State) (i : N.Inputs) :
  R.v20321 (state s) (inputs i) = Zmod.unsigned (N.v20321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20321 s i)) at 1.
  unfold R.v20321, N.v20321.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20322 (s : N.State) (i : N.Inputs) :
  R.v20322 (state s) (inputs i) = Zmod.unsigned (N.v20322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20322 s i)) at 1.
  unfold R.v20322, N.v20322.
  rewrite ?node_7007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20323 (s : N.State) (i : N.Inputs) :
  R.v20323 (state s) (inputs i) = Zmod.unsigned (N.v20323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20323 s i)) at 1.
  unfold R.v20323, N.v20323.
  unfold R.v16463, N.v16463.
  rewrite !state_r437_nr_5F437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r437_nr_5F437 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20324 (s : N.State) (i : N.Inputs) :
  R.v20324 (state s) (inputs i) = Zmod.unsigned (N.v20324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20324 s i)) at 1.
  unfold R.v20324, N.v20324.
  unfold R.v16463, N.v16463.
  rewrite !state_r436_nr_5F436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r436_nr_5F436 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20325 (s : N.State) (i : N.Inputs) :
  R.v20325 (state s) (inputs i) = Zmod.unsigned (N.v20325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20325 s i)) at 1.
  unfold R.v20325, N.v20325.
  unfold R.v6, N.v6.
  rewrite !state_r435_nr_5F435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r435_nr_5F435 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20326 (s : N.State) (i : N.Inputs) :
  R.v20326 (state s) (inputs i) = Zmod.unsigned (N.v20326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20326 s i)) at 1.
  unfold R.v20326, N.v20326.
  unfold R.v6, N.v6.
  rewrite !state_r434_nr_5F434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r434_nr_5F434 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20327 (s : N.State) (i : N.Inputs) :
  R.v20327 (state s) (inputs i) = Zmod.unsigned (N.v20327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20327 s i)) at 1.
  unfold R.v20327, N.v20327.
  rewrite ?node_20325.
  rewrite ?node_20326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20328 (s : N.State) (i : N.Inputs) :
  R.v20328 (state s) (inputs i) = Zmod.unsigned (N.v20328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20328 s i)) at 1.
  unfold R.v20328, N.v20328.
  unfold R.v16484, N.v16484.
  rewrite ?node_20327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20329 (s : N.State) (i : N.Inputs) :
  R.v20329 (state s) (inputs i) = Zmod.unsigned (N.v20329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20329 s i)) at 1.
  unfold R.v20329, N.v20329.
  rewrite ?node_20322.
  rewrite ?node_20323.
  rewrite ?node_20324.
  rewrite ?node_20328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20330 (s : N.State) (i : N.Inputs) :
  R.v20330 (state s) (inputs i) = Zmod.unsigned (N.v20330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20330 s i)) at 1.
  unfold R.v20330, N.v20330.
  unfold R.v6, N.v6.
  rewrite ?node_20329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20331 (s : N.State) (i : N.Inputs) :
  R.v20331 (state s) (inputs i) = Zmod.unsigned (N.v20331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20331 s i)) at 1.
  unfold R.v20331, N.v20331.
  rewrite ?node_7008.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20332 (s : N.State) (i : N.Inputs) :
  R.v20332 (state s) (inputs i) = Zmod.unsigned (N.v20332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20332 s i)) at 1.
  unfold R.v20332, N.v20332.
  unfold R.v6, N.v6.
  rewrite ?node_7106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20333 (s : N.State) (i : N.Inputs) :
  R.v20333 (state s) (inputs i) = Zmod.unsigned (N.v20333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20333 s i)) at 1.
  unfold R.v20333, N.v20333.
  unfold R.v6, N.v6.
  rewrite ?node_7131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20334 (s : N.State) (i : N.Inputs) :
  R.v20334 (state s) (inputs i) = Zmod.unsigned (N.v20334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20334 s i)) at 1.
  unfold R.v20334, N.v20334.
  rewrite ?node_20331.
  rewrite ?node_20332.
  rewrite ?node_20333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20335 (s : N.State) (i : N.Inputs) :
  R.v20335 (state s) (inputs i) = Zmod.unsigned (N.v20335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20335 s i)) at 1.
  unfold R.v20335, N.v20335.
  rewrite ?node_20330.
  rewrite ?node_20334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20336 (s : N.State) (i : N.Inputs) :
  R.v20336 (state s) (inputs i) = Zmod.unsigned (N.v20336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20336 s i)) at 1.
  unfold R.v20336, N.v20336.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20337 (s : N.State) (i : N.Inputs) :
  R.v20337 (state s) (inputs i) = Zmod.unsigned (N.v20337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20337 s i)) at 1.
  unfold R.v20337, N.v20337.
  unfold R.v16463, N.v16463.
  rewrite !state_r436_nr_5F436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r436_nr_5F436 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20338 (s : N.State) (i : N.Inputs) :
  R.v20338 (state s) (inputs i) = Zmod.unsigned (N.v20338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20338 s i)) at 1.
  unfold R.v20338, N.v20338.
  unfold R.v6, N.v6.
  rewrite !state_r435_nr_5F435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r435_nr_5F435 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20339 (s : N.State) (i : N.Inputs) :
  R.v20339 (state s) (inputs i) = Zmod.unsigned (N.v20339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20339 s i)) at 1.
  unfold R.v20339, N.v20339.
  unfold R.v6, N.v6.
  rewrite !state_r434_nr_5F434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r434_nr_5F434 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20340 (s : N.State) (i : N.Inputs) :
  R.v20340 (state s) (inputs i) = Zmod.unsigned (N.v20340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20340 s i)) at 1.
  unfold R.v20340, N.v20340.
  rewrite ?node_20338.
  rewrite ?node_20339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20341 (s : N.State) (i : N.Inputs) :
  R.v20341 (state s) (inputs i) = Zmod.unsigned (N.v20341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20341 s i)) at 1.
  unfold R.v20341, N.v20341.
  unfold R.v16484, N.v16484.
  rewrite ?node_20340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20342 (s : N.State) (i : N.Inputs) :
  R.v20342 (state s) (inputs i) = Zmod.unsigned (N.v20342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20342 s i)) at 1.
  unfold R.v20342, N.v20342.
  rewrite ?node_20337.
  rewrite ?node_20341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20343 (s : N.State) (i : N.Inputs) :
  R.v20343 (state s) (inputs i) = Zmod.unsigned (N.v20343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20343 s i)) at 1.
  unfold R.v20343, N.v20343.
  unfold R.v6, N.v6.
  rewrite ?node_20342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20344 (s : N.State) (i : N.Inputs) :
  R.v20344 (state s) (inputs i) = Zmod.unsigned (N.v20344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20344 s i)) at 1.
  unfold R.v20344, N.v20344.
  rewrite ?node_7003.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20345 (s : N.State) (i : N.Inputs) :
  R.v20345 (state s) (inputs i) = Zmod.unsigned (N.v20345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20345 s i)) at 1.
  unfold R.v20345, N.v20345.
  unfold R.v6, N.v6.
  rewrite ?node_7106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20346 (s : N.State) (i : N.Inputs) :
  R.v20346 (state s) (inputs i) = Zmod.unsigned (N.v20346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20346 s i)) at 1.
  unfold R.v20346, N.v20346.
  rewrite ?node_20344.
  rewrite ?node_20345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20347 (s : N.State) (i : N.Inputs) :
  R.v20347 (state s) (inputs i) = Zmod.unsigned (N.v20347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20347 s i)) at 1.
  unfold R.v20347, N.v20347.
  rewrite ?node_20343.
  rewrite ?node_20346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20348 (s : N.State) (i : N.Inputs) :
  R.v20348 (state s) (inputs i) = Zmod.unsigned (N.v20348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20348 s i)) at 1.
  unfold R.v20348, N.v20348.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20349 (s : N.State) (i : N.Inputs) :
  R.v20349 (state s) (inputs i) = Zmod.unsigned (N.v20349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20349 s i)) at 1.
  unfold R.v20349, N.v20349.
  rewrite ?node_7007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20350 (s : N.State) (i : N.Inputs) :
  R.v20350 (state s) (inputs i) = Zmod.unsigned (N.v20350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20350 s i)) at 1.
  unfold R.v20350, N.v20350.
  unfold R.v6, N.v6.
  rewrite !state_r437_nr_5F437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r437_nr_5F437 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20351 (s : N.State) (i : N.Inputs) :
  R.v20351 (state s) (inputs i) = Zmod.unsigned (N.v20351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20351 s i)) at 1.
  unfold R.v20351, N.v20351.
  unfold R.v6, N.v6.
  rewrite ?node_7003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20352 (s : N.State) (i : N.Inputs) :
  R.v20352 (state s) (inputs i) = Zmod.unsigned (N.v20352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20352 s i)) at 1.
  unfold R.v20352, N.v20352.
  rewrite ?node_20350.
  rewrite ?node_20351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20353 (s : N.State) (i : N.Inputs) :
  R.v20353 (state s) (inputs i) = Zmod.unsigned (N.v20353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20353 s i)) at 1.
  unfold R.v20353, N.v20353.
  unfold R.v16484, N.v16484.
  rewrite ?node_20352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20354 (s : N.State) (i : N.Inputs) :
  R.v20354 (state s) (inputs i) = Zmod.unsigned (N.v20354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20354 s i)) at 1.
  unfold R.v20354, N.v20354.
  rewrite ?node_20349.
  rewrite ?node_20353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20355 (s : N.State) (i : N.Inputs) :
  R.v20355 (state s) (inputs i) = Zmod.unsigned (N.v20355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20355 s i)) at 1.
  unfold R.v20355, N.v20355.
  unfold R.v6, N.v6.
  rewrite ?node_20354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20356 (s : N.State) (i : N.Inputs) :
  R.v20356 (state s) (inputs i) = Zmod.unsigned (N.v20356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20356 s i)) at 1.
  unfold R.v20356, N.v20356.
  rewrite ?node_7008.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20357 (s : N.State) (i : N.Inputs) :
  R.v20357 (state s) (inputs i) = Zmod.unsigned (N.v20357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20357 s i)) at 1.
  unfold R.v20357, N.v20357.
  unfold R.v6, N.v6.
  rewrite ?node_7131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20358 (s : N.State) (i : N.Inputs) :
  R.v20358 (state s) (inputs i) = Zmod.unsigned (N.v20358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20358 s i)) at 1.
  unfold R.v20358, N.v20358.
  rewrite ?node_20356.
  rewrite ?node_20357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20359 (s : N.State) (i : N.Inputs) :
  R.v20359 (state s) (inputs i) = Zmod.unsigned (N.v20359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20359 s i)) at 1.
  unfold R.v20359, N.v20359.
  rewrite ?node_20355.
  rewrite ?node_20358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20360 (s : N.State) (i : N.Inputs) :
  R.v20360 (state s) (inputs i) = Zmod.unsigned (N.v20360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20360 s i)) at 1.
  unfold R.v20360, N.v20360.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20361 (s : N.State) (i : N.Inputs) :
  R.v20361 (state s) (inputs i) = Zmod.unsigned (N.v20361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20361 s i)) at 1.
  unfold R.v20361, N.v20361.
  rewrite ?node_7071.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20362 (s : N.State) (i : N.Inputs) :
  R.v20362 (state s) (inputs i) = Zmod.unsigned (N.v20362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20362 s i)) at 1.
  unfold R.v20362, N.v20362.
  unfold R.v16463, N.v16463.
  rewrite !state_r442_nr_5F442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r442_nr_5F442 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20363 (s : N.State) (i : N.Inputs) :
  R.v20363 (state s) (inputs i) = Zmod.unsigned (N.v20363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20363 s i)) at 1.
  unfold R.v20363, N.v20363.
  unfold R.v16463, N.v16463.
  rewrite !state_r441_nr_5F441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r441_nr_5F441 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20364 (s : N.State) (i : N.Inputs) :
  R.v20364 (state s) (inputs i) = Zmod.unsigned (N.v20364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20364 s i)) at 1.
  unfold R.v20364, N.v20364.
  unfold R.v6, N.v6.
  rewrite !state_r440_nr_5F440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r440_nr_5F440 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20365 (s : N.State) (i : N.Inputs) :
  R.v20365 (state s) (inputs i) = Zmod.unsigned (N.v20365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20365 s i)) at 1.
  unfold R.v20365, N.v20365.
  unfold R.v6, N.v6.
  rewrite !state_r439_nr_5F439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r439_nr_5F439 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20366 (s : N.State) (i : N.Inputs) :
  R.v20366 (state s) (inputs i) = Zmod.unsigned (N.v20366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20366 s i)) at 1.
  unfold R.v20366, N.v20366.
  rewrite ?node_20364.
  rewrite ?node_20365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20367 (s : N.State) (i : N.Inputs) :
  R.v20367 (state s) (inputs i) = Zmod.unsigned (N.v20367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20367 s i)) at 1.
  unfold R.v20367, N.v20367.
  unfold R.v16484, N.v16484.
  rewrite ?node_20366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20368 (s : N.State) (i : N.Inputs) :
  R.v20368 (state s) (inputs i) = Zmod.unsigned (N.v20368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20368 s i)) at 1.
  unfold R.v20368, N.v20368.
  rewrite ?node_20361.
  rewrite ?node_20362.
  rewrite ?node_20363.
  rewrite ?node_20367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20369 (s : N.State) (i : N.Inputs) :
  R.v20369 (state s) (inputs i) = Zmod.unsigned (N.v20369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20369 s i)) at 1.
  unfold R.v20369, N.v20369.
  unfold R.v6, N.v6.
  rewrite ?node_20368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20370 (s : N.State) (i : N.Inputs) :
  R.v20370 (state s) (inputs i) = Zmod.unsigned (N.v20370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20370 s i)) at 1.
  unfold R.v20370, N.v20370.
  rewrite ?node_7072.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20371 (s : N.State) (i : N.Inputs) :
  R.v20371 (state s) (inputs i) = Zmod.unsigned (N.v20371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20371 s i)) at 1.
  unfold R.v20371, N.v20371.
  unfold R.v6, N.v6.
  rewrite ?node_7172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20372 (s : N.State) (i : N.Inputs) :
  R.v20372 (state s) (inputs i) = Zmod.unsigned (N.v20372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20372 s i)) at 1.
  unfold R.v20372, N.v20372.
  unfold R.v6, N.v6.
  rewrite ?node_7213.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20373 (s : N.State) (i : N.Inputs) :
  R.v20373 (state s) (inputs i) = Zmod.unsigned (N.v20373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20373 s i)) at 1.
  unfold R.v20373, N.v20373.
  rewrite ?node_20370.
  rewrite ?node_20371.
  rewrite ?node_20372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20374 (s : N.State) (i : N.Inputs) :
  R.v20374 (state s) (inputs i) = Zmod.unsigned (N.v20374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20374 s i)) at 1.
  unfold R.v20374, N.v20374.
  rewrite ?node_20369.
  rewrite ?node_20373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20375 (s : N.State) (i : N.Inputs) :
  R.v20375 (state s) (inputs i) = Zmod.unsigned (N.v20375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20375 s i)) at 1.
  unfold R.v20375, N.v20375.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20376 (s : N.State) (i : N.Inputs) :
  R.v20376 (state s) (inputs i) = Zmod.unsigned (N.v20376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20376 s i)) at 1.
  unfold R.v20376, N.v20376.
  unfold R.v16463, N.v16463.
  rewrite !state_r441_nr_5F441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r441_nr_5F441 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20377 (s : N.State) (i : N.Inputs) :
  R.v20377 (state s) (inputs i) = Zmod.unsigned (N.v20377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20377 s i)) at 1.
  unfold R.v20377, N.v20377.
  unfold R.v6, N.v6.
  rewrite !state_r440_nr_5F440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r440_nr_5F440 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20378 (s : N.State) (i : N.Inputs) :
  R.v20378 (state s) (inputs i) = Zmod.unsigned (N.v20378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20378 s i)) at 1.
  unfold R.v20378, N.v20378.
  unfold R.v6, N.v6.
  rewrite !state_r439_nr_5F439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r439_nr_5F439 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20379 (s : N.State) (i : N.Inputs) :
  R.v20379 (state s) (inputs i) = Zmod.unsigned (N.v20379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20379 s i)) at 1.
  unfold R.v20379, N.v20379.
  rewrite ?node_20377.
  rewrite ?node_20378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20380 (s : N.State) (i : N.Inputs) :
  R.v20380 (state s) (inputs i) = Zmod.unsigned (N.v20380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20380 s i)) at 1.
  unfold R.v20380, N.v20380.
  unfold R.v16484, N.v16484.
  rewrite ?node_20379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20381 (s : N.State) (i : N.Inputs) :
  R.v20381 (state s) (inputs i) = Zmod.unsigned (N.v20381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20381 s i)) at 1.
  unfold R.v20381, N.v20381.
  rewrite ?node_20376.
  rewrite ?node_20380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20382 (s : N.State) (i : N.Inputs) :
  R.v20382 (state s) (inputs i) = Zmod.unsigned (N.v20382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20382 s i)) at 1.
  unfold R.v20382, N.v20382.
  unfold R.v6, N.v6.
  rewrite ?node_20381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20383 (s : N.State) (i : N.Inputs) :
  R.v20383 (state s) (inputs i) = Zmod.unsigned (N.v20383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20383 s i)) at 1.
  unfold R.v20383, N.v20383.
  rewrite ?node_7067.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20384 (s : N.State) (i : N.Inputs) :
  R.v20384 (state s) (inputs i) = Zmod.unsigned (N.v20384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20384 s i)) at 1.
  unfold R.v20384, N.v20384.
  unfold R.v6, N.v6.
  rewrite ?node_7172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20385 (s : N.State) (i : N.Inputs) :
  R.v20385 (state s) (inputs i) = Zmod.unsigned (N.v20385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20385 s i)) at 1.
  unfold R.v20385, N.v20385.
  rewrite ?node_20383.
  rewrite ?node_20384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20386 (s : N.State) (i : N.Inputs) :
  R.v20386 (state s) (inputs i) = Zmod.unsigned (N.v20386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20386 s i)) at 1.
  unfold R.v20386, N.v20386.
  rewrite ?node_20382.
  rewrite ?node_20385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20387 (s : N.State) (i : N.Inputs) :
  R.v20387 (state s) (inputs i) = Zmod.unsigned (N.v20387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20387 s i)) at 1.
  unfold R.v20387, N.v20387.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20388 (s : N.State) (i : N.Inputs) :
  R.v20388 (state s) (inputs i) = Zmod.unsigned (N.v20388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20388 s i)) at 1.
  unfold R.v20388, N.v20388.
  rewrite ?node_7071.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20389 (s : N.State) (i : N.Inputs) :
  R.v20389 (state s) (inputs i) = Zmod.unsigned (N.v20389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20389 s i)) at 1.
  unfold R.v20389, N.v20389.
  unfold R.v6, N.v6.
  rewrite !state_r442_nr_5F442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r442_nr_5F442 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20390 (s : N.State) (i : N.Inputs) :
  R.v20390 (state s) (inputs i) = Zmod.unsigned (N.v20390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20390 s i)) at 1.
  unfold R.v20390, N.v20390.
  unfold R.v6, N.v6.
  rewrite ?node_7067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20391 (s : N.State) (i : N.Inputs) :
  R.v20391 (state s) (inputs i) = Zmod.unsigned (N.v20391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20391 s i)) at 1.
  unfold R.v20391, N.v20391.
  rewrite ?node_20389.
  rewrite ?node_20390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20392 (s : N.State) (i : N.Inputs) :
  R.v20392 (state s) (inputs i) = Zmod.unsigned (N.v20392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20392 s i)) at 1.
  unfold R.v20392, N.v20392.
  unfold R.v16484, N.v16484.
  rewrite ?node_20391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20393 (s : N.State) (i : N.Inputs) :
  R.v20393 (state s) (inputs i) = Zmod.unsigned (N.v20393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20393 s i)) at 1.
  unfold R.v20393, N.v20393.
  rewrite ?node_20388.
  rewrite ?node_20392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20394 (s : N.State) (i : N.Inputs) :
  R.v20394 (state s) (inputs i) = Zmod.unsigned (N.v20394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20394 s i)) at 1.
  unfold R.v20394, N.v20394.
  unfold R.v6, N.v6.
  rewrite ?node_20393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20395 (s : N.State) (i : N.Inputs) :
  R.v20395 (state s) (inputs i) = Zmod.unsigned (N.v20395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20395 s i)) at 1.
  unfold R.v20395, N.v20395.
  rewrite ?node_7072.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20396 (s : N.State) (i : N.Inputs) :
  R.v20396 (state s) (inputs i) = Zmod.unsigned (N.v20396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20396 s i)) at 1.
  unfold R.v20396, N.v20396.
  unfold R.v6, N.v6.
  rewrite ?node_7213.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20397 (s : N.State) (i : N.Inputs) :
  R.v20397 (state s) (inputs i) = Zmod.unsigned (N.v20397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20397 s i)) at 1.
  unfold R.v20397, N.v20397.
  rewrite ?node_20395.
  rewrite ?node_20396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20398 (s : N.State) (i : N.Inputs) :
  R.v20398 (state s) (inputs i) = Zmod.unsigned (N.v20398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20398 s i)) at 1.
  unfold R.v20398, N.v20398.
  rewrite ?node_20394.
  rewrite ?node_20397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20399 (s : N.State) (i : N.Inputs) :
  R.v20399 (state s) (inputs i) = Zmod.unsigned (N.v20399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20399 s i)) at 1.
  unfold R.v20399, N.v20399.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20400 (s : N.State) (i : N.Inputs) :
  R.v20400 (state s) (inputs i) = Zmod.unsigned (N.v20400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20400 s i)) at 1.
  unfold R.v20400, N.v20400.
  rewrite ?node_7078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20401 (s : N.State) (i : N.Inputs) :
  R.v20401 (state s) (inputs i) = Zmod.unsigned (N.v20401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20401 s i)) at 1.
  unfold R.v20401, N.v20401.
  unfold R.v16463, N.v16463.
  rewrite !state_r446_nr_5F446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r446_nr_5F446 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20402 (s : N.State) (i : N.Inputs) :
  R.v20402 (state s) (inputs i) = Zmod.unsigned (N.v20402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20402 s i)) at 1.
  unfold R.v20402, N.v20402.
  unfold R.v16463, N.v16463.
  rewrite !state_r445_nr_5F445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r445_nr_5F445 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20403 (s : N.State) (i : N.Inputs) :
  R.v20403 (state s) (inputs i) = Zmod.unsigned (N.v20403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20403 s i)) at 1.
  unfold R.v20403, N.v20403.
  unfold R.v6, N.v6.
  rewrite !state_r444_nr_5F444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r444_nr_5F444 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20404 (s : N.State) (i : N.Inputs) :
  R.v20404 (state s) (inputs i) = Zmod.unsigned (N.v20404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20404 s i)) at 1.
  unfold R.v20404, N.v20404.
  unfold R.v6, N.v6.
  rewrite !state_r443_nr_5F443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r443_nr_5F443 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20405 (s : N.State) (i : N.Inputs) :
  R.v20405 (state s) (inputs i) = Zmod.unsigned (N.v20405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20405 s i)) at 1.
  unfold R.v20405, N.v20405.
  rewrite ?node_20403.
  rewrite ?node_20404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20406 (s : N.State) (i : N.Inputs) :
  R.v20406 (state s) (inputs i) = Zmod.unsigned (N.v20406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20406 s i)) at 1.
  unfold R.v20406, N.v20406.
  unfold R.v16484, N.v16484.
  rewrite ?node_20405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20407 (s : N.State) (i : N.Inputs) :
  R.v20407 (state s) (inputs i) = Zmod.unsigned (N.v20407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20407 s i)) at 1.
  unfold R.v20407, N.v20407.
  rewrite ?node_20400.
  rewrite ?node_20401.
  rewrite ?node_20402.
  rewrite ?node_20406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20408 (s : N.State) (i : N.Inputs) :
  R.v20408 (state s) (inputs i) = Zmod.unsigned (N.v20408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20408 s i)) at 1.
  unfold R.v20408, N.v20408.
  unfold R.v6, N.v6.
  rewrite ?node_20407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20409 (s : N.State) (i : N.Inputs) :
  R.v20409 (state s) (inputs i) = Zmod.unsigned (N.v20409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20409 s i)) at 1.
  unfold R.v20409, N.v20409.
  rewrite ?node_7079.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20410 (s : N.State) (i : N.Inputs) :
  R.v20410 (state s) (inputs i) = Zmod.unsigned (N.v20410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20410 s i)) at 1.
  unfold R.v20410, N.v20410.
  unfold R.v6, N.v6.
  rewrite ?node_7179.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20411 (s : N.State) (i : N.Inputs) :
  R.v20411 (state s) (inputs i) = Zmod.unsigned (N.v20411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20411 s i)) at 1.
  unfold R.v20411, N.v20411.
  unfold R.v6, N.v6.
  rewrite ?node_7217.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20412 (s : N.State) (i : N.Inputs) :
  R.v20412 (state s) (inputs i) = Zmod.unsigned (N.v20412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20412 s i)) at 1.
  unfold R.v20412, N.v20412.
  rewrite ?node_20409.
  rewrite ?node_20410.
  rewrite ?node_20411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20413 (s : N.State) (i : N.Inputs) :
  R.v20413 (state s) (inputs i) = Zmod.unsigned (N.v20413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20413 s i)) at 1.
  unfold R.v20413, N.v20413.
  rewrite ?node_20408.
  rewrite ?node_20412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20414 (s : N.State) (i : N.Inputs) :
  R.v20414 (state s) (inputs i) = Zmod.unsigned (N.v20414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20414 s i)) at 1.
  unfold R.v20414, N.v20414.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20415 (s : N.State) (i : N.Inputs) :
  R.v20415 (state s) (inputs i) = Zmod.unsigned (N.v20415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20415 s i)) at 1.
  unfold R.v20415, N.v20415.
  unfold R.v16463, N.v16463.
  rewrite !state_r445_nr_5F445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r445_nr_5F445 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20416 (s : N.State) (i : N.Inputs) :
  R.v20416 (state s) (inputs i) = Zmod.unsigned (N.v20416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20416 s i)) at 1.
  unfold R.v20416, N.v20416.
  unfold R.v6, N.v6.
  rewrite !state_r444_nr_5F444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r444_nr_5F444 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20417 (s : N.State) (i : N.Inputs) :
  R.v20417 (state s) (inputs i) = Zmod.unsigned (N.v20417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20417 s i)) at 1.
  unfold R.v20417, N.v20417.
  unfold R.v6, N.v6.
  rewrite !state_r443_nr_5F443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r443_nr_5F443 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20418 (s : N.State) (i : N.Inputs) :
  R.v20418 (state s) (inputs i) = Zmod.unsigned (N.v20418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20418 s i)) at 1.
  unfold R.v20418, N.v20418.
  rewrite ?node_20416.
  rewrite ?node_20417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20419 (s : N.State) (i : N.Inputs) :
  R.v20419 (state s) (inputs i) = Zmod.unsigned (N.v20419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20419 s i)) at 1.
  unfold R.v20419, N.v20419.
  unfold R.v16484, N.v16484.
  rewrite ?node_20418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20420 (s : N.State) (i : N.Inputs) :
  R.v20420 (state s) (inputs i) = Zmod.unsigned (N.v20420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20420 s i)) at 1.
  unfold R.v20420, N.v20420.
  rewrite ?node_20415.
  rewrite ?node_20419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20421 (s : N.State) (i : N.Inputs) :
  R.v20421 (state s) (inputs i) = Zmod.unsigned (N.v20421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20421 s i)) at 1.
  unfold R.v20421, N.v20421.
  unfold R.v6, N.v6.
  rewrite ?node_20420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20422 (s : N.State) (i : N.Inputs) :
  R.v20422 (state s) (inputs i) = Zmod.unsigned (N.v20422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20422 s i)) at 1.
  unfold R.v20422, N.v20422.
  rewrite ?node_7074.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20423 (s : N.State) (i : N.Inputs) :
  R.v20423 (state s) (inputs i) = Zmod.unsigned (N.v20423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20423 s i)) at 1.
  unfold R.v20423, N.v20423.
  unfold R.v6, N.v6.
  rewrite ?node_7179.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20424 (s : N.State) (i : N.Inputs) :
  R.v20424 (state s) (inputs i) = Zmod.unsigned (N.v20424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20424 s i)) at 1.
  unfold R.v20424, N.v20424.
  rewrite ?node_20422.
  rewrite ?node_20423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20425 (s : N.State) (i : N.Inputs) :
  R.v20425 (state s) (inputs i) = Zmod.unsigned (N.v20425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20425 s i)) at 1.
  unfold R.v20425, N.v20425.
  rewrite ?node_20421.
  rewrite ?node_20424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20426 (s : N.State) (i : N.Inputs) :
  R.v20426 (state s) (inputs i) = Zmod.unsigned (N.v20426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20426 s i)) at 1.
  unfold R.v20426, N.v20426.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20427 (s : N.State) (i : N.Inputs) :
  R.v20427 (state s) (inputs i) = Zmod.unsigned (N.v20427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20427 s i)) at 1.
  unfold R.v20427, N.v20427.
  rewrite ?node_7078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20428 (s : N.State) (i : N.Inputs) :
  R.v20428 (state s) (inputs i) = Zmod.unsigned (N.v20428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20428 s i)) at 1.
  unfold R.v20428, N.v20428.
  unfold R.v6, N.v6.
  rewrite !state_r446_nr_5F446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r446_nr_5F446 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20429 (s : N.State) (i : N.Inputs) :
  R.v20429 (state s) (inputs i) = Zmod.unsigned (N.v20429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20429 s i)) at 1.
  unfold R.v20429, N.v20429.
  unfold R.v6, N.v6.
  rewrite ?node_7074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20430 (s : N.State) (i : N.Inputs) :
  R.v20430 (state s) (inputs i) = Zmod.unsigned (N.v20430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20430 s i)) at 1.
  unfold R.v20430, N.v20430.
  rewrite ?node_20428.
  rewrite ?node_20429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20431 (s : N.State) (i : N.Inputs) :
  R.v20431 (state s) (inputs i) = Zmod.unsigned (N.v20431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20431 s i)) at 1.
  unfold R.v20431, N.v20431.
  unfold R.v16484, N.v16484.
  rewrite ?node_20430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20432 (s : N.State) (i : N.Inputs) :
  R.v20432 (state s) (inputs i) = Zmod.unsigned (N.v20432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20432 s i)) at 1.
  unfold R.v20432, N.v20432.
  rewrite ?node_20427.
  rewrite ?node_20431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20433 (s : N.State) (i : N.Inputs) :
  R.v20433 (state s) (inputs i) = Zmod.unsigned (N.v20433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20433 s i)) at 1.
  unfold R.v20433, N.v20433.
  unfold R.v6, N.v6.
  rewrite ?node_20432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20434 (s : N.State) (i : N.Inputs) :
  R.v20434 (state s) (inputs i) = Zmod.unsigned (N.v20434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20434 s i)) at 1.
  unfold R.v20434, N.v20434.
  rewrite ?node_7079.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20435 (s : N.State) (i : N.Inputs) :
  R.v20435 (state s) (inputs i) = Zmod.unsigned (N.v20435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20435 s i)) at 1.
  unfold R.v20435, N.v20435.
  unfold R.v6, N.v6.
  rewrite ?node_7217.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20436 (s : N.State) (i : N.Inputs) :
  R.v20436 (state s) (inputs i) = Zmod.unsigned (N.v20436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20436 s i)) at 1.
  unfold R.v20436, N.v20436.
  rewrite ?node_20434.
  rewrite ?node_20435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20437 (s : N.State) (i : N.Inputs) :
  R.v20437 (state s) (inputs i) = Zmod.unsigned (N.v20437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20437 s i)) at 1.
  unfold R.v20437, N.v20437.
  rewrite ?node_20433.
  rewrite ?node_20436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20438 (s : N.State) (i : N.Inputs) :
  R.v20438 (state s) (inputs i) = Zmod.unsigned (N.v20438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20438 s i)) at 1.
  unfold R.v20438, N.v20438.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20439 (s : N.State) (i : N.Inputs) :
  R.v20439 (state s) (inputs i) = Zmod.unsigned (N.v20439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20439 s i)) at 1.
  unfold R.v20439, N.v20439.
  rewrite ?node_7086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20440 (s : N.State) (i : N.Inputs) :
  R.v20440 (state s) (inputs i) = Zmod.unsigned (N.v20440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20440 s i)) at 1.
  unfold R.v20440, N.v20440.
  unfold R.v16463, N.v16463.
  rewrite !state_r450_nr_5F450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r450_nr_5F450 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20441 (s : N.State) (i : N.Inputs) :
  R.v20441 (state s) (inputs i) = Zmod.unsigned (N.v20441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20441 s i)) at 1.
  unfold R.v20441, N.v20441.
  unfold R.v16463, N.v16463.
  rewrite !state_r449_nr_5F449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r449_nr_5F449 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20442 (s : N.State) (i : N.Inputs) :
  R.v20442 (state s) (inputs i) = Zmod.unsigned (N.v20442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20442 s i)) at 1.
  unfold R.v20442, N.v20442.
  unfold R.v6, N.v6.
  rewrite !state_r448_nr_5F448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r448_nr_5F448 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20443 (s : N.State) (i : N.Inputs) :
  R.v20443 (state s) (inputs i) = Zmod.unsigned (N.v20443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20443 s i)) at 1.
  unfold R.v20443, N.v20443.
  unfold R.v6, N.v6.
  rewrite !state_r447_nr_5F447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r447_nr_5F447 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20444 (s : N.State) (i : N.Inputs) :
  R.v20444 (state s) (inputs i) = Zmod.unsigned (N.v20444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20444 s i)) at 1.
  unfold R.v20444, N.v20444.
  rewrite ?node_20442.
  rewrite ?node_20443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20445 (s : N.State) (i : N.Inputs) :
  R.v20445 (state s) (inputs i) = Zmod.unsigned (N.v20445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20445 s i)) at 1.
  unfold R.v20445, N.v20445.
  unfold R.v16484, N.v16484.
  rewrite ?node_20444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20446 (s : N.State) (i : N.Inputs) :
  R.v20446 (state s) (inputs i) = Zmod.unsigned (N.v20446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20446 s i)) at 1.
  unfold R.v20446, N.v20446.
  rewrite ?node_20439.
  rewrite ?node_20440.
  rewrite ?node_20441.
  rewrite ?node_20445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20447 (s : N.State) (i : N.Inputs) :
  R.v20447 (state s) (inputs i) = Zmod.unsigned (N.v20447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20447 s i)) at 1.
  unfold R.v20447, N.v20447.
  unfold R.v6, N.v6.
  rewrite ?node_20446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20448 (s : N.State) (i : N.Inputs) :
  R.v20448 (state s) (inputs i) = Zmod.unsigned (N.v20448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20448 s i)) at 1.
  unfold R.v20448, N.v20448.
  rewrite ?node_7087.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20449 (s : N.State) (i : N.Inputs) :
  R.v20449 (state s) (inputs i) = Zmod.unsigned (N.v20449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20449 s i)) at 1.
  unfold R.v20449, N.v20449.
  unfold R.v6, N.v6.
  rewrite ?node_7187.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20450 (s : N.State) (i : N.Inputs) :
  R.v20450 (state s) (inputs i) = Zmod.unsigned (N.v20450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20450 s i)) at 1.
  unfold R.v20450, N.v20450.
  unfold R.v6, N.v6.
  rewrite ?node_7226.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20451 (s : N.State) (i : N.Inputs) :
  R.v20451 (state s) (inputs i) = Zmod.unsigned (N.v20451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20451 s i)) at 1.
  unfold R.v20451, N.v20451.
  rewrite ?node_20448.
  rewrite ?node_20449.
  rewrite ?node_20450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20452 (s : N.State) (i : N.Inputs) :
  R.v20452 (state s) (inputs i) = Zmod.unsigned (N.v20452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20452 s i)) at 1.
  unfold R.v20452, N.v20452.
  rewrite ?node_20447.
  rewrite ?node_20451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20453 (s : N.State) (i : N.Inputs) :
  R.v20453 (state s) (inputs i) = Zmod.unsigned (N.v20453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20453 s i)) at 1.
  unfold R.v20453, N.v20453.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20454 (s : N.State) (i : N.Inputs) :
  R.v20454 (state s) (inputs i) = Zmod.unsigned (N.v20454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20454 s i)) at 1.
  unfold R.v20454, N.v20454.
  unfold R.v16463, N.v16463.
  rewrite !state_r449_nr_5F449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r449_nr_5F449 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20455 (s : N.State) (i : N.Inputs) :
  R.v20455 (state s) (inputs i) = Zmod.unsigned (N.v20455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20455 s i)) at 1.
  unfold R.v20455, N.v20455.
  unfold R.v6, N.v6.
  rewrite !state_r448_nr_5F448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r448_nr_5F448 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20456 (s : N.State) (i : N.Inputs) :
  R.v20456 (state s) (inputs i) = Zmod.unsigned (N.v20456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20456 s i)) at 1.
  unfold R.v20456, N.v20456.
  unfold R.v6, N.v6.
  rewrite !state_r447_nr_5F447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r447_nr_5F447 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20457 (s : N.State) (i : N.Inputs) :
  R.v20457 (state s) (inputs i) = Zmod.unsigned (N.v20457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20457 s i)) at 1.
  unfold R.v20457, N.v20457.
  rewrite ?node_20455.
  rewrite ?node_20456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20458 (s : N.State) (i : N.Inputs) :
  R.v20458 (state s) (inputs i) = Zmod.unsigned (N.v20458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20458 s i)) at 1.
  unfold R.v20458, N.v20458.
  unfold R.v16484, N.v16484.
  rewrite ?node_20457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20459 (s : N.State) (i : N.Inputs) :
  R.v20459 (state s) (inputs i) = Zmod.unsigned (N.v20459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20459 s i)) at 1.
  unfold R.v20459, N.v20459.
  rewrite ?node_20454.
  rewrite ?node_20458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20460 (s : N.State) (i : N.Inputs) :
  R.v20460 (state s) (inputs i) = Zmod.unsigned (N.v20460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20460 s i)) at 1.
  unfold R.v20460, N.v20460.
  unfold R.v6, N.v6.
  rewrite ?node_20459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20461 (s : N.State) (i : N.Inputs) :
  R.v20461 (state s) (inputs i) = Zmod.unsigned (N.v20461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20461 s i)) at 1.
  unfold R.v20461, N.v20461.
  rewrite ?node_7082.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20462 (s : N.State) (i : N.Inputs) :
  R.v20462 (state s) (inputs i) = Zmod.unsigned (N.v20462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20462 s i)) at 1.
  unfold R.v20462, N.v20462.
  unfold R.v6, N.v6.
  rewrite ?node_7187.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20463 (s : N.State) (i : N.Inputs) :
  R.v20463 (state s) (inputs i) = Zmod.unsigned (N.v20463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20463 s i)) at 1.
  unfold R.v20463, N.v20463.
  rewrite ?node_20461.
  rewrite ?node_20462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20464 (s : N.State) (i : N.Inputs) :
  R.v20464 (state s) (inputs i) = Zmod.unsigned (N.v20464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20464 s i)) at 1.
  unfold R.v20464, N.v20464.
  rewrite ?node_20460.
  rewrite ?node_20463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20465 (s : N.State) (i : N.Inputs) :
  R.v20465 (state s) (inputs i) = Zmod.unsigned (N.v20465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20465 s i)) at 1.
  unfold R.v20465, N.v20465.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20466 (s : N.State) (i : N.Inputs) :
  R.v20466 (state s) (inputs i) = Zmod.unsigned (N.v20466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20466 s i)) at 1.
  unfold R.v20466, N.v20466.
  rewrite ?node_7086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20467 (s : N.State) (i : N.Inputs) :
  R.v20467 (state s) (inputs i) = Zmod.unsigned (N.v20467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20467 s i)) at 1.
  unfold R.v20467, N.v20467.
  unfold R.v6, N.v6.
  rewrite !state_r450_nr_5F450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r450_nr_5F450 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20468 (s : N.State) (i : N.Inputs) :
  R.v20468 (state s) (inputs i) = Zmod.unsigned (N.v20468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20468 s i)) at 1.
  unfold R.v20468, N.v20468.
  unfold R.v6, N.v6.
  rewrite ?node_7082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20469 (s : N.State) (i : N.Inputs) :
  R.v20469 (state s) (inputs i) = Zmod.unsigned (N.v20469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20469 s i)) at 1.
  unfold R.v20469, N.v20469.
  rewrite ?node_20467.
  rewrite ?node_20468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20470 (s : N.State) (i : N.Inputs) :
  R.v20470 (state s) (inputs i) = Zmod.unsigned (N.v20470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20470 s i)) at 1.
  unfold R.v20470, N.v20470.
  unfold R.v16484, N.v16484.
  rewrite ?node_20469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20471 (s : N.State) (i : N.Inputs) :
  R.v20471 (state s) (inputs i) = Zmod.unsigned (N.v20471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20471 s i)) at 1.
  unfold R.v20471, N.v20471.
  rewrite ?node_20466.
  rewrite ?node_20470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20472 (s : N.State) (i : N.Inputs) :
  R.v20472 (state s) (inputs i) = Zmod.unsigned (N.v20472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20472 s i)) at 1.
  unfold R.v20472, N.v20472.
  unfold R.v6, N.v6.
  rewrite ?node_20471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20473 (s : N.State) (i : N.Inputs) :
  R.v20473 (state s) (inputs i) = Zmod.unsigned (N.v20473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20473 s i)) at 1.
  unfold R.v20473, N.v20473.
  rewrite ?node_7087.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20474 (s : N.State) (i : N.Inputs) :
  R.v20474 (state s) (inputs i) = Zmod.unsigned (N.v20474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20474 s i)) at 1.
  unfold R.v20474, N.v20474.
  unfold R.v6, N.v6.
  rewrite ?node_7226.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20475 (s : N.State) (i : N.Inputs) :
  R.v20475 (state s) (inputs i) = Zmod.unsigned (N.v20475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20475 s i)) at 1.
  unfold R.v20475, N.v20475.
  rewrite ?node_20473.
  rewrite ?node_20474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20476 (s : N.State) (i : N.Inputs) :
  R.v20476 (state s) (inputs i) = Zmod.unsigned (N.v20476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20476 s i)) at 1.
  unfold R.v20476, N.v20476.
  rewrite ?node_20472.
  rewrite ?node_20475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20477 (s : N.State) (i : N.Inputs) :
  R.v20477 (state s) (inputs i) = Zmod.unsigned (N.v20477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20477 s i)) at 1.
  unfold R.v20477, N.v20477.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20478 (s : N.State) (i : N.Inputs) :
  R.v20478 (state s) (inputs i) = Zmod.unsigned (N.v20478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20478 s i)) at 1.
  unfold R.v20478, N.v20478.
  rewrite ?node_7094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20479 (s : N.State) (i : N.Inputs) :
  R.v20479 (state s) (inputs i) = Zmod.unsigned (N.v20479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20479 s i)) at 1.
  unfold R.v20479, N.v20479.
  unfold R.v16463, N.v16463.
  rewrite !state_r454_nr_5F454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r454_nr_5F454 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20480 (s : N.State) (i : N.Inputs) :
  R.v20480 (state s) (inputs i) = Zmod.unsigned (N.v20480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20480 s i)) at 1.
  unfold R.v20480, N.v20480.
  unfold R.v16463, N.v16463.
  rewrite !state_r453_nr_5F453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r453_nr_5F453 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20481 (s : N.State) (i : N.Inputs) :
  R.v20481 (state s) (inputs i) = Zmod.unsigned (N.v20481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20481 s i)) at 1.
  unfold R.v20481, N.v20481.
  unfold R.v6, N.v6.
  rewrite !state_r452_nr_5F452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r452_nr_5F452 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20482 (s : N.State) (i : N.Inputs) :
  R.v20482 (state s) (inputs i) = Zmod.unsigned (N.v20482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20482 s i)) at 1.
  unfold R.v20482, N.v20482.
  unfold R.v6, N.v6.
  rewrite !state_r451_nr_5F451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r451_nr_5F451 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20483 (s : N.State) (i : N.Inputs) :
  R.v20483 (state s) (inputs i) = Zmod.unsigned (N.v20483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20483 s i)) at 1.
  unfold R.v20483, N.v20483.
  rewrite ?node_20481.
  rewrite ?node_20482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20484 (s : N.State) (i : N.Inputs) :
  R.v20484 (state s) (inputs i) = Zmod.unsigned (N.v20484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20484 s i)) at 1.
  unfold R.v20484, N.v20484.
  unfold R.v16484, N.v16484.
  rewrite ?node_20483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20485 (s : N.State) (i : N.Inputs) :
  R.v20485 (state s) (inputs i) = Zmod.unsigned (N.v20485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20485 s i)) at 1.
  unfold R.v20485, N.v20485.
  rewrite ?node_20478.
  rewrite ?node_20479.
  rewrite ?node_20480.
  rewrite ?node_20484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20486 (s : N.State) (i : N.Inputs) :
  R.v20486 (state s) (inputs i) = Zmod.unsigned (N.v20486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20486 s i)) at 1.
  unfold R.v20486, N.v20486.
  unfold R.v6, N.v6.
  rewrite ?node_20485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20487 (s : N.State) (i : N.Inputs) :
  R.v20487 (state s) (inputs i) = Zmod.unsigned (N.v20487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20487 s i)) at 1.
  unfold R.v20487, N.v20487.
  rewrite ?node_7095.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20488 (s : N.State) (i : N.Inputs) :
  R.v20488 (state s) (inputs i) = Zmod.unsigned (N.v20488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20488 s i)) at 1.
  unfold R.v20488, N.v20488.
  unfold R.v6, N.v6.
  rewrite ?node_7195.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20489 (s : N.State) (i : N.Inputs) :
  R.v20489 (state s) (inputs i) = Zmod.unsigned (N.v20489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20489 s i)) at 1.
  unfold R.v20489, N.v20489.
  unfold R.v6, N.v6.
  rewrite ?node_7229.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20490 (s : N.State) (i : N.Inputs) :
  R.v20490 (state s) (inputs i) = Zmod.unsigned (N.v20490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20490 s i)) at 1.
  unfold R.v20490, N.v20490.
  rewrite ?node_20487.
  rewrite ?node_20488.
  rewrite ?node_20489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20491 (s : N.State) (i : N.Inputs) :
  R.v20491 (state s) (inputs i) = Zmod.unsigned (N.v20491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20491 s i)) at 1.
  unfold R.v20491, N.v20491.
  rewrite ?node_20486.
  rewrite ?node_20490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20492 (s : N.State) (i : N.Inputs) :
  R.v20492 (state s) (inputs i) = Zmod.unsigned (N.v20492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20492 s i)) at 1.
  unfold R.v20492, N.v20492.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20493 (s : N.State) (i : N.Inputs) :
  R.v20493 (state s) (inputs i) = Zmod.unsigned (N.v20493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20493 s i)) at 1.
  unfold R.v20493, N.v20493.
  unfold R.v16463, N.v16463.
  rewrite !state_r453_nr_5F453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r453_nr_5F453 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20494 (s : N.State) (i : N.Inputs) :
  R.v20494 (state s) (inputs i) = Zmod.unsigned (N.v20494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20494 s i)) at 1.
  unfold R.v20494, N.v20494.
  unfold R.v6, N.v6.
  rewrite !state_r452_nr_5F452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r452_nr_5F452 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20495 (s : N.State) (i : N.Inputs) :
  R.v20495 (state s) (inputs i) = Zmod.unsigned (N.v20495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20495 s i)) at 1.
  unfold R.v20495, N.v20495.
  unfold R.v6, N.v6.
  rewrite !state_r451_nr_5F451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r451_nr_5F451 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20496 (s : N.State) (i : N.Inputs) :
  R.v20496 (state s) (inputs i) = Zmod.unsigned (N.v20496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20496 s i)) at 1.
  unfold R.v20496, N.v20496.
  rewrite ?node_20494.
  rewrite ?node_20495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20497 (s : N.State) (i : N.Inputs) :
  R.v20497 (state s) (inputs i) = Zmod.unsigned (N.v20497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20497 s i)) at 1.
  unfold R.v20497, N.v20497.
  unfold R.v16484, N.v16484.
  rewrite ?node_20496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20498 (s : N.State) (i : N.Inputs) :
  R.v20498 (state s) (inputs i) = Zmod.unsigned (N.v20498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20498 s i)) at 1.
  unfold R.v20498, N.v20498.
  rewrite ?node_20493.
  rewrite ?node_20497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20499 (s : N.State) (i : N.Inputs) :
  R.v20499 (state s) (inputs i) = Zmod.unsigned (N.v20499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20499 s i)) at 1.
  unfold R.v20499, N.v20499.
  unfold R.v6, N.v6.
  rewrite ?node_20498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20500 (s : N.State) (i : N.Inputs) :
  R.v20500 (state s) (inputs i) = Zmod.unsigned (N.v20500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20500 s i)) at 1.
  unfold R.v20500, N.v20500.
  rewrite ?node_7090.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20501 (s : N.State) (i : N.Inputs) :
  R.v20501 (state s) (inputs i) = Zmod.unsigned (N.v20501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20501 s i)) at 1.
  unfold R.v20501, N.v20501.
  unfold R.v6, N.v6.
  rewrite ?node_7195.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20502 (s : N.State) (i : N.Inputs) :
  R.v20502 (state s) (inputs i) = Zmod.unsigned (N.v20502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20502 s i)) at 1.
  unfold R.v20502, N.v20502.
  rewrite ?node_20500.
  rewrite ?node_20501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20503 (s : N.State) (i : N.Inputs) :
  R.v20503 (state s) (inputs i) = Zmod.unsigned (N.v20503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20503 s i)) at 1.
  unfold R.v20503, N.v20503.
  rewrite ?node_20499.
  rewrite ?node_20502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20504 (s : N.State) (i : N.Inputs) :
  R.v20504 (state s) (inputs i) = Zmod.unsigned (N.v20504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20504 s i)) at 1.
  unfold R.v20504, N.v20504.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20505 (s : N.State) (i : N.Inputs) :
  R.v20505 (state s) (inputs i) = Zmod.unsigned (N.v20505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20505 s i)) at 1.
  unfold R.v20505, N.v20505.
  rewrite ?node_7094.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20506 (s : N.State) (i : N.Inputs) :
  R.v20506 (state s) (inputs i) = Zmod.unsigned (N.v20506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20506 s i)) at 1.
  unfold R.v20506, N.v20506.
  unfold R.v6, N.v6.
  rewrite !state_r454_nr_5F454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r454_nr_5F454 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20507 (s : N.State) (i : N.Inputs) :
  R.v20507 (state s) (inputs i) = Zmod.unsigned (N.v20507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20507 s i)) at 1.
  unfold R.v20507, N.v20507.
  unfold R.v6, N.v6.
  rewrite ?node_7090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20508 (s : N.State) (i : N.Inputs) :
  R.v20508 (state s) (inputs i) = Zmod.unsigned (N.v20508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20508 s i)) at 1.
  unfold R.v20508, N.v20508.
  rewrite ?node_20506.
  rewrite ?node_20507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20509 (s : N.State) (i : N.Inputs) :
  R.v20509 (state s) (inputs i) = Zmod.unsigned (N.v20509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20509 s i)) at 1.
  unfold R.v20509, N.v20509.
  unfold R.v16484, N.v16484.
  rewrite ?node_20508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20510 (s : N.State) (i : N.Inputs) :
  R.v20510 (state s) (inputs i) = Zmod.unsigned (N.v20510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20510 s i)) at 1.
  unfold R.v20510, N.v20510.
  rewrite ?node_20505.
  rewrite ?node_20509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20511 (s : N.State) (i : N.Inputs) :
  R.v20511 (state s) (inputs i) = Zmod.unsigned (N.v20511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20511 s i)) at 1.
  unfold R.v20511, N.v20511.
  unfold R.v6, N.v6.
  rewrite ?node_20510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20512 (s : N.State) (i : N.Inputs) :
  R.v20512 (state s) (inputs i) = Zmod.unsigned (N.v20512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20512 s i)) at 1.
  unfold R.v20512, N.v20512.
  rewrite ?node_7095.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20513 (s : N.State) (i : N.Inputs) :
  R.v20513 (state s) (inputs i) = Zmod.unsigned (N.v20513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20513 s i)) at 1.
  unfold R.v20513, N.v20513.
  unfold R.v6, N.v6.
  rewrite ?node_7229.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20514 (s : N.State) (i : N.Inputs) :
  R.v20514 (state s) (inputs i) = Zmod.unsigned (N.v20514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20514 s i)) at 1.
  unfold R.v20514, N.v20514.
  rewrite ?node_20512.
  rewrite ?node_20513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20515 (s : N.State) (i : N.Inputs) :
  R.v20515 (state s) (inputs i) = Zmod.unsigned (N.v20515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20515 s i)) at 1.
  unfold R.v20515, N.v20515.
  rewrite ?node_20511.
  rewrite ?node_20514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20516 (s : N.State) (i : N.Inputs) :
  R.v20516 (state s) (inputs i) = Zmod.unsigned (N.v20516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20516 s i)) at 1.
  unfold R.v20516, N.v20516.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20517 (s : N.State) (i : N.Inputs) :
  R.v20517 (state s) (inputs i) = Zmod.unsigned (N.v20517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20517 s i)) at 1.
  unfold R.v20517, N.v20517.
  rewrite ?node_7106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20518 (s : N.State) (i : N.Inputs) :
  R.v20518 (state s) (inputs i) = Zmod.unsigned (N.v20518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20518 s i)) at 1.
  unfold R.v20518, N.v20518.
  unfold R.v16463, N.v16463.
  rewrite !state_r458_nr_5F458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r458_nr_5F458 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20519 (s : N.State) (i : N.Inputs) :
  R.v20519 (state s) (inputs i) = Zmod.unsigned (N.v20519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20519 s i)) at 1.
  unfold R.v20519, N.v20519.
  unfold R.v16463, N.v16463.
  rewrite !state_r457_nr_5F457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r457_nr_5F457 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20520 (s : N.State) (i : N.Inputs) :
  R.v20520 (state s) (inputs i) = Zmod.unsigned (N.v20520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20520 s i)) at 1.
  unfold R.v20520, N.v20520.
  unfold R.v6, N.v6.
  rewrite !state_r456_nr_5F456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r456_nr_5F456 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20521 (s : N.State) (i : N.Inputs) :
  R.v20521 (state s) (inputs i) = Zmod.unsigned (N.v20521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20521 s i)) at 1.
  unfold R.v20521, N.v20521.
  unfold R.v6, N.v6.
  rewrite !state_r455_nr_5F455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r455_nr_5F455 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20522 (s : N.State) (i : N.Inputs) :
  R.v20522 (state s) (inputs i) = Zmod.unsigned (N.v20522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20522 s i)) at 1.
  unfold R.v20522, N.v20522.
  rewrite ?node_20520.
  rewrite ?node_20521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20523 (s : N.State) (i : N.Inputs) :
  R.v20523 (state s) (inputs i) = Zmod.unsigned (N.v20523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20523 s i)) at 1.
  unfold R.v20523, N.v20523.
  unfold R.v16484, N.v16484.
  rewrite ?node_20522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20524 (s : N.State) (i : N.Inputs) :
  R.v20524 (state s) (inputs i) = Zmod.unsigned (N.v20524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20524 s i)) at 1.
  unfold R.v20524, N.v20524.
  rewrite ?node_20517.
  rewrite ?node_20518.
  rewrite ?node_20519.
  rewrite ?node_20523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20525 (s : N.State) (i : N.Inputs) :
  R.v20525 (state s) (inputs i) = Zmod.unsigned (N.v20525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20525 s i)) at 1.
  unfold R.v20525, N.v20525.
  unfold R.v6, N.v6.
  rewrite ?node_20524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20526 (s : N.State) (i : N.Inputs) :
  R.v20526 (state s) (inputs i) = Zmod.unsigned (N.v20526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20526 s i)) at 1.
  unfold R.v20526, N.v20526.
  rewrite ?node_7107.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20527 (s : N.State) (i : N.Inputs) :
  R.v20527 (state s) (inputs i) = Zmod.unsigned (N.v20527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20527 s i)) at 1.
  unfold R.v20527, N.v20527.
  unfold R.v6, N.v6.
  rewrite ?node_7207.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20528 (s : N.State) (i : N.Inputs) :
  R.v20528 (state s) (inputs i) = Zmod.unsigned (N.v20528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20528 s i)) at 1.
  unfold R.v20528, N.v20528.
  unfold R.v6, N.v6.
  rewrite ?node_7233.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20529 (s : N.State) (i : N.Inputs) :
  R.v20529 (state s) (inputs i) = Zmod.unsigned (N.v20529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20529 s i)) at 1.
  unfold R.v20529, N.v20529.
  rewrite ?node_20526.
  rewrite ?node_20527.
  rewrite ?node_20528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20530 (s : N.State) (i : N.Inputs) :
  R.v20530 (state s) (inputs i) = Zmod.unsigned (N.v20530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20530 s i)) at 1.
  unfold R.v20530, N.v20530.
  rewrite ?node_20525.
  rewrite ?node_20529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20531 (s : N.State) (i : N.Inputs) :
  R.v20531 (state s) (inputs i) = Zmod.unsigned (N.v20531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20531 s i)) at 1.
  unfold R.v20531, N.v20531.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20532 (s : N.State) (i : N.Inputs) :
  R.v20532 (state s) (inputs i) = Zmod.unsigned (N.v20532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20532 s i)) at 1.
  unfold R.v20532, N.v20532.
  unfold R.v16463, N.v16463.
  rewrite !state_r457_nr_5F457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r457_nr_5F457 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20533 (s : N.State) (i : N.Inputs) :
  R.v20533 (state s) (inputs i) = Zmod.unsigned (N.v20533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20533 s i)) at 1.
  unfold R.v20533, N.v20533.
  unfold R.v6, N.v6.
  rewrite !state_r456_nr_5F456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r456_nr_5F456 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20534 (s : N.State) (i : N.Inputs) :
  R.v20534 (state s) (inputs i) = Zmod.unsigned (N.v20534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20534 s i)) at 1.
  unfold R.v20534, N.v20534.
  unfold R.v6, N.v6.
  rewrite !state_r455_nr_5F455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r455_nr_5F455 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20535 (s : N.State) (i : N.Inputs) :
  R.v20535 (state s) (inputs i) = Zmod.unsigned (N.v20535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20535 s i)) at 1.
  unfold R.v20535, N.v20535.
  rewrite ?node_20533.
  rewrite ?node_20534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20536 (s : N.State) (i : N.Inputs) :
  R.v20536 (state s) (inputs i) = Zmod.unsigned (N.v20536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20536 s i)) at 1.
  unfold R.v20536, N.v20536.
  unfold R.v16484, N.v16484.
  rewrite ?node_20535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20537 (s : N.State) (i : N.Inputs) :
  R.v20537 (state s) (inputs i) = Zmod.unsigned (N.v20537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20537 s i)) at 1.
  unfold R.v20537, N.v20537.
  rewrite ?node_20532.
  rewrite ?node_20536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20538 (s : N.State) (i : N.Inputs) :
  R.v20538 (state s) (inputs i) = Zmod.unsigned (N.v20538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20538 s i)) at 1.
  unfold R.v20538, N.v20538.
  unfold R.v6, N.v6.
  rewrite ?node_20537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20539 (s : N.State) (i : N.Inputs) :
  R.v20539 (state s) (inputs i) = Zmod.unsigned (N.v20539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20539 s i)) at 1.
  unfold R.v20539, N.v20539.
  rewrite ?node_7102.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20540 (s : N.State) (i : N.Inputs) :
  R.v20540 (state s) (inputs i) = Zmod.unsigned (N.v20540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20540 s i)) at 1.
  unfold R.v20540, N.v20540.
  unfold R.v6, N.v6.
  rewrite ?node_7207.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20541 (s : N.State) (i : N.Inputs) :
  R.v20541 (state s) (inputs i) = Zmod.unsigned (N.v20541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20541 s i)) at 1.
  unfold R.v20541, N.v20541.
  rewrite ?node_20539.
  rewrite ?node_20540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20542 (s : N.State) (i : N.Inputs) :
  R.v20542 (state s) (inputs i) = Zmod.unsigned (N.v20542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20542 s i)) at 1.
  unfold R.v20542, N.v20542.
  rewrite ?node_20538.
  rewrite ?node_20541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20543 (s : N.State) (i : N.Inputs) :
  R.v20543 (state s) (inputs i) = Zmod.unsigned (N.v20543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20543 s i)) at 1.
  unfold R.v20543, N.v20543.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20544 (s : N.State) (i : N.Inputs) :
  R.v20544 (state s) (inputs i) = Zmod.unsigned (N.v20544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20544 s i)) at 1.
  unfold R.v20544, N.v20544.
  rewrite ?node_7106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20545 (s : N.State) (i : N.Inputs) :
  R.v20545 (state s) (inputs i) = Zmod.unsigned (N.v20545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20545 s i)) at 1.
  unfold R.v20545, N.v20545.
  unfold R.v6, N.v6.
  rewrite !state_r458_nr_5F458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r458_nr_5F458 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20546 (s : N.State) (i : N.Inputs) :
  R.v20546 (state s) (inputs i) = Zmod.unsigned (N.v20546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20546 s i)) at 1.
  unfold R.v20546, N.v20546.
  unfold R.v6, N.v6.
  rewrite ?node_7102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20547 (s : N.State) (i : N.Inputs) :
  R.v20547 (state s) (inputs i) = Zmod.unsigned (N.v20547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20547 s i)) at 1.
  unfold R.v20547, N.v20547.
  rewrite ?node_20545.
  rewrite ?node_20546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20548 (s : N.State) (i : N.Inputs) :
  R.v20548 (state s) (inputs i) = Zmod.unsigned (N.v20548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20548 s i)) at 1.
  unfold R.v20548, N.v20548.
  unfold R.v16484, N.v16484.
  rewrite ?node_20547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20549 (s : N.State) (i : N.Inputs) :
  R.v20549 (state s) (inputs i) = Zmod.unsigned (N.v20549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20549 s i)) at 1.
  unfold R.v20549, N.v20549.
  rewrite ?node_20544.
  rewrite ?node_20548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20550 (s : N.State) (i : N.Inputs) :
  R.v20550 (state s) (inputs i) = Zmod.unsigned (N.v20550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20550 s i)) at 1.
  unfold R.v20550, N.v20550.
  unfold R.v6, N.v6.
  rewrite ?node_20549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20551 (s : N.State) (i : N.Inputs) :
  R.v20551 (state s) (inputs i) = Zmod.unsigned (N.v20551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20551 s i)) at 1.
  unfold R.v20551, N.v20551.
  rewrite ?node_7107.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20552 (s : N.State) (i : N.Inputs) :
  R.v20552 (state s) (inputs i) = Zmod.unsigned (N.v20552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20552 s i)) at 1.
  unfold R.v20552, N.v20552.
  unfold R.v6, N.v6.
  rewrite ?node_7233.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20553 (s : N.State) (i : N.Inputs) :
  R.v20553 (state s) (inputs i) = Zmod.unsigned (N.v20553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20553 s i)) at 1.
  unfold R.v20553, N.v20553.
  rewrite ?node_20551.
  rewrite ?node_20552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20554 (s : N.State) (i : N.Inputs) :
  R.v20554 (state s) (inputs i) = Zmod.unsigned (N.v20554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20554 s i)) at 1.
  unfold R.v20554, N.v20554.
  rewrite ?node_20550.
  rewrite ?node_20553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20555 (s : N.State) (i : N.Inputs) :
  R.v20555 (state s) (inputs i) = Zmod.unsigned (N.v20555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20555 s i)) at 1.
  unfold R.v20555, N.v20555.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20556 (s : N.State) (i : N.Inputs) :
  R.v20556 (state s) (inputs i) = Zmod.unsigned (N.v20556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20556 s i)) at 1.
  unfold R.v20556, N.v20556.
  rewrite ?node_7172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20557 (s : N.State) (i : N.Inputs) :
  R.v20557 (state s) (inputs i) = Zmod.unsigned (N.v20557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20557 s i)) at 1.
  unfold R.v20557, N.v20557.
  unfold R.v16463, N.v16463.
  rewrite !state_r463_nr_5F463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r463_nr_5F463 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20558 (s : N.State) (i : N.Inputs) :
  R.v20558 (state s) (inputs i) = Zmod.unsigned (N.v20558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20558 s i)) at 1.
  unfold R.v20558, N.v20558.
  unfold R.v16463, N.v16463.
  rewrite !state_r462_nr_5F462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r462_nr_5F462 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20559 (s : N.State) (i : N.Inputs) :
  R.v20559 (state s) (inputs i) = Zmod.unsigned (N.v20559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20559 s i)) at 1.
  unfold R.v20559, N.v20559.
  unfold R.v6, N.v6.
  rewrite !state_r461_nr_5F461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r461_nr_5F461 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20560 (s : N.State) (i : N.Inputs) :
  R.v20560 (state s) (inputs i) = Zmod.unsigned (N.v20560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20560 s i)) at 1.
  unfold R.v20560, N.v20560.
  unfold R.v6, N.v6.
  rewrite !state_r460_nr_5F460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r460_nr_5F460 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20561 (s : N.State) (i : N.Inputs) :
  R.v20561 (state s) (inputs i) = Zmod.unsigned (N.v20561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20561 s i)) at 1.
  unfold R.v20561, N.v20561.
  rewrite ?node_20559.
  rewrite ?node_20560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20562 (s : N.State) (i : N.Inputs) :
  R.v20562 (state s) (inputs i) = Zmod.unsigned (N.v20562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20562 s i)) at 1.
  unfold R.v20562, N.v20562.
  unfold R.v16484, N.v16484.
  rewrite ?node_20561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20563 (s : N.State) (i : N.Inputs) :
  R.v20563 (state s) (inputs i) = Zmod.unsigned (N.v20563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20563 s i)) at 1.
  unfold R.v20563, N.v20563.
  rewrite ?node_20556.
  rewrite ?node_20557.
  rewrite ?node_20558.
  rewrite ?node_20562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20564 (s : N.State) (i : N.Inputs) :
  R.v20564 (state s) (inputs i) = Zmod.unsigned (N.v20564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20564 s i)) at 1.
  unfold R.v20564, N.v20564.
  unfold R.v6, N.v6.
  rewrite ?node_20563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20565 (s : N.State) (i : N.Inputs) :
  R.v20565 (state s) (inputs i) = Zmod.unsigned (N.v20565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20565 s i)) at 1.
  unfold R.v20565, N.v20565.
  rewrite ?node_7173.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20566 (s : N.State) (i : N.Inputs) :
  R.v20566 (state s) (inputs i) = Zmod.unsigned (N.v20566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20566 s i)) at 1.
  unfold R.v20566, N.v20566.
  unfold R.v6, N.v6.
  rewrite ?node_7274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20567 (s : N.State) (i : N.Inputs) :
  R.v20567 (state s) (inputs i) = Zmod.unsigned (N.v20567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20567 s i)) at 1.
  unfold R.v20567, N.v20567.
  unfold R.v6, N.v6.
  rewrite ?node_7315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20568 (s : N.State) (i : N.Inputs) :
  R.v20568 (state s) (inputs i) = Zmod.unsigned (N.v20568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20568 s i)) at 1.
  unfold R.v20568, N.v20568.
  rewrite ?node_20565.
  rewrite ?node_20566.
  rewrite ?node_20567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20569 (s : N.State) (i : N.Inputs) :
  R.v20569 (state s) (inputs i) = Zmod.unsigned (N.v20569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20569 s i)) at 1.
  unfold R.v20569, N.v20569.
  rewrite ?node_20564.
  rewrite ?node_20568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20570 (s : N.State) (i : N.Inputs) :
  R.v20570 (state s) (inputs i) = Zmod.unsigned (N.v20570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20570 s i)) at 1.
  unfold R.v20570, N.v20570.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20571 (s : N.State) (i : N.Inputs) :
  R.v20571 (state s) (inputs i) = Zmod.unsigned (N.v20571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20571 s i)) at 1.
  unfold R.v20571, N.v20571.
  unfold R.v16463, N.v16463.
  rewrite !state_r462_nr_5F462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r462_nr_5F462 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20572 (s : N.State) (i : N.Inputs) :
  R.v20572 (state s) (inputs i) = Zmod.unsigned (N.v20572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20572 s i)) at 1.
  unfold R.v20572, N.v20572.
  unfold R.v6, N.v6.
  rewrite !state_r461_nr_5F461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r461_nr_5F461 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20573 (s : N.State) (i : N.Inputs) :
  R.v20573 (state s) (inputs i) = Zmod.unsigned (N.v20573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20573 s i)) at 1.
  unfold R.v20573, N.v20573.
  unfold R.v6, N.v6.
  rewrite !state_r460_nr_5F460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r460_nr_5F460 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20574 (s : N.State) (i : N.Inputs) :
  R.v20574 (state s) (inputs i) = Zmod.unsigned (N.v20574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20574 s i)) at 1.
  unfold R.v20574, N.v20574.
  rewrite ?node_20572.
  rewrite ?node_20573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20575 (s : N.State) (i : N.Inputs) :
  R.v20575 (state s) (inputs i) = Zmod.unsigned (N.v20575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20575 s i)) at 1.
  unfold R.v20575, N.v20575.
  unfold R.v16484, N.v16484.
  rewrite ?node_20574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20576 (s : N.State) (i : N.Inputs) :
  R.v20576 (state s) (inputs i) = Zmod.unsigned (N.v20576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20576 s i)) at 1.
  unfold R.v20576, N.v20576.
  rewrite ?node_20571.
  rewrite ?node_20575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20577 (s : N.State) (i : N.Inputs) :
  R.v20577 (state s) (inputs i) = Zmod.unsigned (N.v20577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20577 s i)) at 1.
  unfold R.v20577, N.v20577.
  unfold R.v6, N.v6.
  rewrite ?node_20576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20578 (s : N.State) (i : N.Inputs) :
  R.v20578 (state s) (inputs i) = Zmod.unsigned (N.v20578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20578 s i)) at 1.
  unfold R.v20578, N.v20578.
  rewrite ?node_7168.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20579 (s : N.State) (i : N.Inputs) :
  R.v20579 (state s) (inputs i) = Zmod.unsigned (N.v20579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20579 s i)) at 1.
  unfold R.v20579, N.v20579.
  unfold R.v6, N.v6.
  rewrite ?node_7274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20580 (s : N.State) (i : N.Inputs) :
  R.v20580 (state s) (inputs i) = Zmod.unsigned (N.v20580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20580 s i)) at 1.
  unfold R.v20580, N.v20580.
  rewrite ?node_20578.
  rewrite ?node_20579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20581 (s : N.State) (i : N.Inputs) :
  R.v20581 (state s) (inputs i) = Zmod.unsigned (N.v20581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20581 s i)) at 1.
  unfold R.v20581, N.v20581.
  rewrite ?node_20577.
  rewrite ?node_20580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20582 (s : N.State) (i : N.Inputs) :
  R.v20582 (state s) (inputs i) = Zmod.unsigned (N.v20582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20582 s i)) at 1.
  unfold R.v20582, N.v20582.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20583 (s : N.State) (i : N.Inputs) :
  R.v20583 (state s) (inputs i) = Zmod.unsigned (N.v20583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20583 s i)) at 1.
  unfold R.v20583, N.v20583.
  rewrite ?node_7172.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20584 (s : N.State) (i : N.Inputs) :
  R.v20584 (state s) (inputs i) = Zmod.unsigned (N.v20584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20584 s i)) at 1.
  unfold R.v20584, N.v20584.
  unfold R.v6, N.v6.
  rewrite !state_r463_nr_5F463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r463_nr_5F463 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20585 (s : N.State) (i : N.Inputs) :
  R.v20585 (state s) (inputs i) = Zmod.unsigned (N.v20585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20585 s i)) at 1.
  unfold R.v20585, N.v20585.
  unfold R.v6, N.v6.
  rewrite ?node_7168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20586 (s : N.State) (i : N.Inputs) :
  R.v20586 (state s) (inputs i) = Zmod.unsigned (N.v20586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20586 s i)) at 1.
  unfold R.v20586, N.v20586.
  rewrite ?node_20584.
  rewrite ?node_20585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20587 (s : N.State) (i : N.Inputs) :
  R.v20587 (state s) (inputs i) = Zmod.unsigned (N.v20587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20587 s i)) at 1.
  unfold R.v20587, N.v20587.
  unfold R.v16484, N.v16484.
  rewrite ?node_20586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20588 (s : N.State) (i : N.Inputs) :
  R.v20588 (state s) (inputs i) = Zmod.unsigned (N.v20588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20588 s i)) at 1.
  unfold R.v20588, N.v20588.
  rewrite ?node_20583.
  rewrite ?node_20587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20589 (s : N.State) (i : N.Inputs) :
  R.v20589 (state s) (inputs i) = Zmod.unsigned (N.v20589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20589 s i)) at 1.
  unfold R.v20589, N.v20589.
  unfold R.v6, N.v6.
  rewrite ?node_20588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20590 (s : N.State) (i : N.Inputs) :
  R.v20590 (state s) (inputs i) = Zmod.unsigned (N.v20590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20590 s i)) at 1.
  unfold R.v20590, N.v20590.
  rewrite ?node_7173.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20591 (s : N.State) (i : N.Inputs) :
  R.v20591 (state s) (inputs i) = Zmod.unsigned (N.v20591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20591 s i)) at 1.
  unfold R.v20591, N.v20591.
  unfold R.v6, N.v6.
  rewrite ?node_7315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20592 (s : N.State) (i : N.Inputs) :
  R.v20592 (state s) (inputs i) = Zmod.unsigned (N.v20592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20592 s i)) at 1.
  unfold R.v20592, N.v20592.
  rewrite ?node_20590.
  rewrite ?node_20591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20593 (s : N.State) (i : N.Inputs) :
  R.v20593 (state s) (inputs i) = Zmod.unsigned (N.v20593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20593 s i)) at 1.
  unfold R.v20593, N.v20593.
  rewrite ?node_20589.
  rewrite ?node_20592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20594 (s : N.State) (i : N.Inputs) :
  R.v20594 (state s) (inputs i) = Zmod.unsigned (N.v20594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20594 s i)) at 1.
  unfold R.v20594, N.v20594.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20595 (s : N.State) (i : N.Inputs) :
  R.v20595 (state s) (inputs i) = Zmod.unsigned (N.v20595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20595 s i)) at 1.
  unfold R.v20595, N.v20595.
  rewrite ?node_7179.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20596 (s : N.State) (i : N.Inputs) :
  R.v20596 (state s) (inputs i) = Zmod.unsigned (N.v20596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20596 s i)) at 1.
  unfold R.v20596, N.v20596.
  unfold R.v16463, N.v16463.
  rewrite !state_r467_nr_5F467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r467_nr_5F467 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20597 (s : N.State) (i : N.Inputs) :
  R.v20597 (state s) (inputs i) = Zmod.unsigned (N.v20597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20597 s i)) at 1.
  unfold R.v20597, N.v20597.
  unfold R.v16463, N.v16463.
  rewrite !state_r466_nr_5F466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r466_nr_5F466 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20598 (s : N.State) (i : N.Inputs) :
  R.v20598 (state s) (inputs i) = Zmod.unsigned (N.v20598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20598 s i)) at 1.
  unfold R.v20598, N.v20598.
  unfold R.v6, N.v6.
  rewrite !state_r465_nr_5F465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r465_nr_5F465 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20599 (s : N.State) (i : N.Inputs) :
  R.v20599 (state s) (inputs i) = Zmod.unsigned (N.v20599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20599 s i)) at 1.
  unfold R.v20599, N.v20599.
  unfold R.v6, N.v6.
  rewrite !state_r464_nr_5F464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r464_nr_5F464 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20600 (s : N.State) (i : N.Inputs) :
  R.v20600 (state s) (inputs i) = Zmod.unsigned (N.v20600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20600 s i)) at 1.
  unfold R.v20600, N.v20600.
  rewrite ?node_20598.
  rewrite ?node_20599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20601 (s : N.State) (i : N.Inputs) :
  R.v20601 (state s) (inputs i) = Zmod.unsigned (N.v20601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20601 s i)) at 1.
  unfold R.v20601, N.v20601.
  unfold R.v16484, N.v16484.
  rewrite ?node_20600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20602 (s : N.State) (i : N.Inputs) :
  R.v20602 (state s) (inputs i) = Zmod.unsigned (N.v20602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20602 s i)) at 1.
  unfold R.v20602, N.v20602.
  rewrite ?node_20595.
  rewrite ?node_20596.
  rewrite ?node_20597.
  rewrite ?node_20601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20603 (s : N.State) (i : N.Inputs) :
  R.v20603 (state s) (inputs i) = Zmod.unsigned (N.v20603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20603 s i)) at 1.
  unfold R.v20603, N.v20603.
  unfold R.v6, N.v6.
  rewrite ?node_20602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20604 (s : N.State) (i : N.Inputs) :
  R.v20604 (state s) (inputs i) = Zmod.unsigned (N.v20604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20604 s i)) at 1.
  unfold R.v20604, N.v20604.
  rewrite ?node_7180.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20605 (s : N.State) (i : N.Inputs) :
  R.v20605 (state s) (inputs i) = Zmod.unsigned (N.v20605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20605 s i)) at 1.
  unfold R.v20605, N.v20605.
  unfold R.v6, N.v6.
  rewrite ?node_7281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20606 (s : N.State) (i : N.Inputs) :
  R.v20606 (state s) (inputs i) = Zmod.unsigned (N.v20606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20606 s i)) at 1.
  unfold R.v20606, N.v20606.
  unfold R.v6, N.v6.
  rewrite ?node_7319.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20607 (s : N.State) (i : N.Inputs) :
  R.v20607 (state s) (inputs i) = Zmod.unsigned (N.v20607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20607 s i)) at 1.
  unfold R.v20607, N.v20607.
  rewrite ?node_20604.
  rewrite ?node_20605.
  rewrite ?node_20606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20608 (s : N.State) (i : N.Inputs) :
  R.v20608 (state s) (inputs i) = Zmod.unsigned (N.v20608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20608 s i)) at 1.
  unfold R.v20608, N.v20608.
  rewrite ?node_20603.
  rewrite ?node_20607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20609 (s : N.State) (i : N.Inputs) :
  R.v20609 (state s) (inputs i) = Zmod.unsigned (N.v20609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20609 s i)) at 1.
  unfold R.v20609, N.v20609.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20610 (s : N.State) (i : N.Inputs) :
  R.v20610 (state s) (inputs i) = Zmod.unsigned (N.v20610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20610 s i)) at 1.
  unfold R.v20610, N.v20610.
  unfold R.v16463, N.v16463.
  rewrite !state_r466_nr_5F466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r466_nr_5F466 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20611 (s : N.State) (i : N.Inputs) :
  R.v20611 (state s) (inputs i) = Zmod.unsigned (N.v20611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20611 s i)) at 1.
  unfold R.v20611, N.v20611.
  unfold R.v6, N.v6.
  rewrite !state_r465_nr_5F465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r465_nr_5F465 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20612 (s : N.State) (i : N.Inputs) :
  R.v20612 (state s) (inputs i) = Zmod.unsigned (N.v20612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20612 s i)) at 1.
  unfold R.v20612, N.v20612.
  unfold R.v6, N.v6.
  rewrite !state_r464_nr_5F464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r464_nr_5F464 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20613 (s : N.State) (i : N.Inputs) :
  R.v20613 (state s) (inputs i) = Zmod.unsigned (N.v20613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20613 s i)) at 1.
  unfold R.v20613, N.v20613.
  rewrite ?node_20611.
  rewrite ?node_20612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20614 (s : N.State) (i : N.Inputs) :
  R.v20614 (state s) (inputs i) = Zmod.unsigned (N.v20614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20614 s i)) at 1.
  unfold R.v20614, N.v20614.
  unfold R.v16484, N.v16484.
  rewrite ?node_20613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20615 (s : N.State) (i : N.Inputs) :
  R.v20615 (state s) (inputs i) = Zmod.unsigned (N.v20615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20615 s i)) at 1.
  unfold R.v20615, N.v20615.
  rewrite ?node_20610.
  rewrite ?node_20614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20616 (s : N.State) (i : N.Inputs) :
  R.v20616 (state s) (inputs i) = Zmod.unsigned (N.v20616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20616 s i)) at 1.
  unfold R.v20616, N.v20616.
  unfold R.v6, N.v6.
  rewrite ?node_20615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20617 (s : N.State) (i : N.Inputs) :
  R.v20617 (state s) (inputs i) = Zmod.unsigned (N.v20617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20617 s i)) at 1.
  unfold R.v20617, N.v20617.
  rewrite ?node_7175.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20618 (s : N.State) (i : N.Inputs) :
  R.v20618 (state s) (inputs i) = Zmod.unsigned (N.v20618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20618 s i)) at 1.
  unfold R.v20618, N.v20618.
  unfold R.v6, N.v6.
  rewrite ?node_7281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20619 (s : N.State) (i : N.Inputs) :
  R.v20619 (state s) (inputs i) = Zmod.unsigned (N.v20619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20619 s i)) at 1.
  unfold R.v20619, N.v20619.
  rewrite ?node_20617.
  rewrite ?node_20618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20620 (s : N.State) (i : N.Inputs) :
  R.v20620 (state s) (inputs i) = Zmod.unsigned (N.v20620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20620 s i)) at 1.
  unfold R.v20620, N.v20620.
  rewrite ?node_20616.
  rewrite ?node_20619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20621 (s : N.State) (i : N.Inputs) :
  R.v20621 (state s) (inputs i) = Zmod.unsigned (N.v20621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20621 s i)) at 1.
  unfold R.v20621, N.v20621.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20622 (s : N.State) (i : N.Inputs) :
  R.v20622 (state s) (inputs i) = Zmod.unsigned (N.v20622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20622 s i)) at 1.
  unfold R.v20622, N.v20622.
  rewrite ?node_7179.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20623 (s : N.State) (i : N.Inputs) :
  R.v20623 (state s) (inputs i) = Zmod.unsigned (N.v20623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20623 s i)) at 1.
  unfold R.v20623, N.v20623.
  unfold R.v6, N.v6.
  rewrite !state_r467_nr_5F467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r467_nr_5F467 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20624 (s : N.State) (i : N.Inputs) :
  R.v20624 (state s) (inputs i) = Zmod.unsigned (N.v20624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20624 s i)) at 1.
  unfold R.v20624, N.v20624.
  unfold R.v6, N.v6.
  rewrite ?node_7175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20625 (s : N.State) (i : N.Inputs) :
  R.v20625 (state s) (inputs i) = Zmod.unsigned (N.v20625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20625 s i)) at 1.
  unfold R.v20625, N.v20625.
  rewrite ?node_20623.
  rewrite ?node_20624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20626 (s : N.State) (i : N.Inputs) :
  R.v20626 (state s) (inputs i) = Zmod.unsigned (N.v20626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20626 s i)) at 1.
  unfold R.v20626, N.v20626.
  unfold R.v16484, N.v16484.
  rewrite ?node_20625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20627 (s : N.State) (i : N.Inputs) :
  R.v20627 (state s) (inputs i) = Zmod.unsigned (N.v20627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20627 s i)) at 1.
  unfold R.v20627, N.v20627.
  rewrite ?node_20622.
  rewrite ?node_20626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20628 (s : N.State) (i : N.Inputs) :
  R.v20628 (state s) (inputs i) = Zmod.unsigned (N.v20628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20628 s i)) at 1.
  unfold R.v20628, N.v20628.
  unfold R.v6, N.v6.
  rewrite ?node_20627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20629 (s : N.State) (i : N.Inputs) :
  R.v20629 (state s) (inputs i) = Zmod.unsigned (N.v20629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20629 s i)) at 1.
  unfold R.v20629, N.v20629.
  rewrite ?node_7180.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20630 (s : N.State) (i : N.Inputs) :
  R.v20630 (state s) (inputs i) = Zmod.unsigned (N.v20630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20630 s i)) at 1.
  unfold R.v20630, N.v20630.
  unfold R.v6, N.v6.
  rewrite ?node_7319.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20631 (s : N.State) (i : N.Inputs) :
  R.v20631 (state s) (inputs i) = Zmod.unsigned (N.v20631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20631 s i)) at 1.
  unfold R.v20631, N.v20631.
  rewrite ?node_20629.
  rewrite ?node_20630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20632 (s : N.State) (i : N.Inputs) :
  R.v20632 (state s) (inputs i) = Zmod.unsigned (N.v20632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20632 s i)) at 1.
  unfold R.v20632, N.v20632.
  rewrite ?node_20628.
  rewrite ?node_20631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20633 (s : N.State) (i : N.Inputs) :
  R.v20633 (state s) (inputs i) = Zmod.unsigned (N.v20633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20633 s i)) at 1.
  unfold R.v20633, N.v20633.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20634 (s : N.State) (i : N.Inputs) :
  R.v20634 (state s) (inputs i) = Zmod.unsigned (N.v20634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20634 s i)) at 1.
  unfold R.v20634, N.v20634.
  rewrite ?node_7187.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20635 (s : N.State) (i : N.Inputs) :
  R.v20635 (state s) (inputs i) = Zmod.unsigned (N.v20635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20635 s i)) at 1.
  unfold R.v20635, N.v20635.
  unfold R.v16463, N.v16463.
  rewrite !state_r471_nr_5F471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r471_nr_5F471 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20636 (s : N.State) (i : N.Inputs) :
  R.v20636 (state s) (inputs i) = Zmod.unsigned (N.v20636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20636 s i)) at 1.
  unfold R.v20636, N.v20636.
  unfold R.v16463, N.v16463.
  rewrite !state_r470_nr_5F470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r470_nr_5F470 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20637 (s : N.State) (i : N.Inputs) :
  R.v20637 (state s) (inputs i) = Zmod.unsigned (N.v20637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20637 s i)) at 1.
  unfold R.v20637, N.v20637.
  unfold R.v6, N.v6.
  rewrite !state_r469_nr_5F469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r469_nr_5F469 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20638 (s : N.State) (i : N.Inputs) :
  R.v20638 (state s) (inputs i) = Zmod.unsigned (N.v20638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20638 s i)) at 1.
  unfold R.v20638, N.v20638.
  unfold R.v6, N.v6.
  rewrite !state_r468_nr_5F468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r468_nr_5F468 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20639 (s : N.State) (i : N.Inputs) :
  R.v20639 (state s) (inputs i) = Zmod.unsigned (N.v20639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20639 s i)) at 1.
  unfold R.v20639, N.v20639.
  rewrite ?node_20637.
  rewrite ?node_20638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20640 (s : N.State) (i : N.Inputs) :
  R.v20640 (state s) (inputs i) = Zmod.unsigned (N.v20640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20640 s i)) at 1.
  unfold R.v20640, N.v20640.
  unfold R.v16484, N.v16484.
  rewrite ?node_20639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20641 (s : N.State) (i : N.Inputs) :
  R.v20641 (state s) (inputs i) = Zmod.unsigned (N.v20641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20641 s i)) at 1.
  unfold R.v20641, N.v20641.
  rewrite ?node_20634.
  rewrite ?node_20635.
  rewrite ?node_20636.
  rewrite ?node_20640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20642 (s : N.State) (i : N.Inputs) :
  R.v20642 (state s) (inputs i) = Zmod.unsigned (N.v20642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20642 s i)) at 1.
  unfold R.v20642, N.v20642.
  unfold R.v6, N.v6.
  rewrite ?node_20641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20643 (s : N.State) (i : N.Inputs) :
  R.v20643 (state s) (inputs i) = Zmod.unsigned (N.v20643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20643 s i)) at 1.
  unfold R.v20643, N.v20643.
  rewrite ?node_7188.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20644 (s : N.State) (i : N.Inputs) :
  R.v20644 (state s) (inputs i) = Zmod.unsigned (N.v20644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20644 s i)) at 1.
  unfold R.v20644, N.v20644.
  unfold R.v6, N.v6.
  rewrite ?node_7289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20645 (s : N.State) (i : N.Inputs) :
  R.v20645 (state s) (inputs i) = Zmod.unsigned (N.v20645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20645 s i)) at 1.
  unfold R.v20645, N.v20645.
  unfold R.v6, N.v6.
  rewrite ?node_7328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20646 (s : N.State) (i : N.Inputs) :
  R.v20646 (state s) (inputs i) = Zmod.unsigned (N.v20646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20646 s i)) at 1.
  unfold R.v20646, N.v20646.
  rewrite ?node_20643.
  rewrite ?node_20644.
  rewrite ?node_20645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20647 (s : N.State) (i : N.Inputs) :
  R.v20647 (state s) (inputs i) = Zmod.unsigned (N.v20647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20647 s i)) at 1.
  unfold R.v20647, N.v20647.
  rewrite ?node_20642.
  rewrite ?node_20646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20648 (s : N.State) (i : N.Inputs) :
  R.v20648 (state s) (inputs i) = Zmod.unsigned (N.v20648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20648 s i)) at 1.
  unfold R.v20648, N.v20648.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20649 (s : N.State) (i : N.Inputs) :
  R.v20649 (state s) (inputs i) = Zmod.unsigned (N.v20649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20649 s i)) at 1.
  unfold R.v20649, N.v20649.
  unfold R.v16463, N.v16463.
  rewrite !state_r470_nr_5F470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r470_nr_5F470 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20650 (s : N.State) (i : N.Inputs) :
  R.v20650 (state s) (inputs i) = Zmod.unsigned (N.v20650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20650 s i)) at 1.
  unfold R.v20650, N.v20650.
  unfold R.v6, N.v6.
  rewrite !state_r469_nr_5F469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r469_nr_5F469 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20651 (s : N.State) (i : N.Inputs) :
  R.v20651 (state s) (inputs i) = Zmod.unsigned (N.v20651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20651 s i)) at 1.
  unfold R.v20651, N.v20651.
  unfold R.v6, N.v6.
  rewrite !state_r468_nr_5F468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r468_nr_5F468 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20652 (s : N.State) (i : N.Inputs) :
  R.v20652 (state s) (inputs i) = Zmod.unsigned (N.v20652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20652 s i)) at 1.
  unfold R.v20652, N.v20652.
  rewrite ?node_20650.
  rewrite ?node_20651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20653 (s : N.State) (i : N.Inputs) :
  R.v20653 (state s) (inputs i) = Zmod.unsigned (N.v20653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20653 s i)) at 1.
  unfold R.v20653, N.v20653.
  unfold R.v16484, N.v16484.
  rewrite ?node_20652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20654 (s : N.State) (i : N.Inputs) :
  R.v20654 (state s) (inputs i) = Zmod.unsigned (N.v20654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20654 s i)) at 1.
  unfold R.v20654, N.v20654.
  rewrite ?node_20649.
  rewrite ?node_20653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20655 (s : N.State) (i : N.Inputs) :
  R.v20655 (state s) (inputs i) = Zmod.unsigned (N.v20655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20655 s i)) at 1.
  unfold R.v20655, N.v20655.
  unfold R.v6, N.v6.
  rewrite ?node_20654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20656 (s : N.State) (i : N.Inputs) :
  R.v20656 (state s) (inputs i) = Zmod.unsigned (N.v20656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20656 s i)) at 1.
  unfold R.v20656, N.v20656.
  rewrite ?node_7183.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20657 (s : N.State) (i : N.Inputs) :
  R.v20657 (state s) (inputs i) = Zmod.unsigned (N.v20657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20657 s i)) at 1.
  unfold R.v20657, N.v20657.
  unfold R.v6, N.v6.
  rewrite ?node_7289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20658 (s : N.State) (i : N.Inputs) :
  R.v20658 (state s) (inputs i) = Zmod.unsigned (N.v20658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20658 s i)) at 1.
  unfold R.v20658, N.v20658.
  rewrite ?node_20656.
  rewrite ?node_20657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20659 (s : N.State) (i : N.Inputs) :
  R.v20659 (state s) (inputs i) = Zmod.unsigned (N.v20659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20659 s i)) at 1.
  unfold R.v20659, N.v20659.
  rewrite ?node_20655.
  rewrite ?node_20658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20660 (s : N.State) (i : N.Inputs) :
  R.v20660 (state s) (inputs i) = Zmod.unsigned (N.v20660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20660 s i)) at 1.
  unfold R.v20660, N.v20660.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20661 (s : N.State) (i : N.Inputs) :
  R.v20661 (state s) (inputs i) = Zmod.unsigned (N.v20661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20661 s i)) at 1.
  unfold R.v20661, N.v20661.
  rewrite ?node_7187.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20662 (s : N.State) (i : N.Inputs) :
  R.v20662 (state s) (inputs i) = Zmod.unsigned (N.v20662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20662 s i)) at 1.
  unfold R.v20662, N.v20662.
  unfold R.v6, N.v6.
  rewrite !state_r471_nr_5F471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r471_nr_5F471 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20663 (s : N.State) (i : N.Inputs) :
  R.v20663 (state s) (inputs i) = Zmod.unsigned (N.v20663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20663 s i)) at 1.
  unfold R.v20663, N.v20663.
  unfold R.v6, N.v6.
  rewrite ?node_7183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20664 (s : N.State) (i : N.Inputs) :
  R.v20664 (state s) (inputs i) = Zmod.unsigned (N.v20664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20664 s i)) at 1.
  unfold R.v20664, N.v20664.
  rewrite ?node_20662.
  rewrite ?node_20663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20665 (s : N.State) (i : N.Inputs) :
  R.v20665 (state s) (inputs i) = Zmod.unsigned (N.v20665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20665 s i)) at 1.
  unfold R.v20665, N.v20665.
  unfold R.v16484, N.v16484.
  rewrite ?node_20664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20666 (s : N.State) (i : N.Inputs) :
  R.v20666 (state s) (inputs i) = Zmod.unsigned (N.v20666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20666 s i)) at 1.
  unfold R.v20666, N.v20666.
  rewrite ?node_20661.
  rewrite ?node_20665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20667 (s : N.State) (i : N.Inputs) :
  R.v20667 (state s) (inputs i) = Zmod.unsigned (N.v20667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20667 s i)) at 1.
  unfold R.v20667, N.v20667.
  unfold R.v6, N.v6.
  rewrite ?node_20666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20668 (s : N.State) (i : N.Inputs) :
  R.v20668 (state s) (inputs i) = Zmod.unsigned (N.v20668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20668 s i)) at 1.
  unfold R.v20668, N.v20668.
  rewrite ?node_7188.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20669 (s : N.State) (i : N.Inputs) :
  R.v20669 (state s) (inputs i) = Zmod.unsigned (N.v20669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20669 s i)) at 1.
  unfold R.v20669, N.v20669.
  unfold R.v6, N.v6.
  rewrite ?node_7328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20670 (s : N.State) (i : N.Inputs) :
  R.v20670 (state s) (inputs i) = Zmod.unsigned (N.v20670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20670 s i)) at 1.
  unfold R.v20670, N.v20670.
  rewrite ?node_20668.
  rewrite ?node_20669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20671 (s : N.State) (i : N.Inputs) :
  R.v20671 (state s) (inputs i) = Zmod.unsigned (N.v20671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20671 s i)) at 1.
  unfold R.v20671, N.v20671.
  rewrite ?node_20667.
  rewrite ?node_20670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20672 (s : N.State) (i : N.Inputs) :
  R.v20672 (state s) (inputs i) = Zmod.unsigned (N.v20672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20672 s i)) at 1.
  unfold R.v20672, N.v20672.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20673 (s : N.State) (i : N.Inputs) :
  R.v20673 (state s) (inputs i) = Zmod.unsigned (N.v20673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20673 s i)) at 1.
  unfold R.v20673, N.v20673.
  rewrite ?node_7195.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20674 (s : N.State) (i : N.Inputs) :
  R.v20674 (state s) (inputs i) = Zmod.unsigned (N.v20674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20674 s i)) at 1.
  unfold R.v20674, N.v20674.
  unfold R.v16463, N.v16463.
  rewrite !state_r475_nr_5F475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r475_nr_5F475 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20675 (s : N.State) (i : N.Inputs) :
  R.v20675 (state s) (inputs i) = Zmod.unsigned (N.v20675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20675 s i)) at 1.
  unfold R.v20675, N.v20675.
  unfold R.v16463, N.v16463.
  rewrite !state_r474_nr_5F474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r474_nr_5F474 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20676 (s : N.State) (i : N.Inputs) :
  R.v20676 (state s) (inputs i) = Zmod.unsigned (N.v20676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20676 s i)) at 1.
  unfold R.v20676, N.v20676.
  unfold R.v6, N.v6.
  rewrite !state_r473_nr_5F473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r473_nr_5F473 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20677 (s : N.State) (i : N.Inputs) :
  R.v20677 (state s) (inputs i) = Zmod.unsigned (N.v20677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20677 s i)) at 1.
  unfold R.v20677, N.v20677.
  unfold R.v6, N.v6.
  rewrite !state_r472_nr_5F472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r472_nr_5F472 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20678 (s : N.State) (i : N.Inputs) :
  R.v20678 (state s) (inputs i) = Zmod.unsigned (N.v20678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20678 s i)) at 1.
  unfold R.v20678, N.v20678.
  rewrite ?node_20676.
  rewrite ?node_20677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20679 (s : N.State) (i : N.Inputs) :
  R.v20679 (state s) (inputs i) = Zmod.unsigned (N.v20679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20679 s i)) at 1.
  unfold R.v20679, N.v20679.
  unfold R.v16484, N.v16484.
  rewrite ?node_20678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20680 (s : N.State) (i : N.Inputs) :
  R.v20680 (state s) (inputs i) = Zmod.unsigned (N.v20680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20680 s i)) at 1.
  unfold R.v20680, N.v20680.
  rewrite ?node_20673.
  rewrite ?node_20674.
  rewrite ?node_20675.
  rewrite ?node_20679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20681 (s : N.State) (i : N.Inputs) :
  R.v20681 (state s) (inputs i) = Zmod.unsigned (N.v20681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20681 s i)) at 1.
  unfold R.v20681, N.v20681.
  unfold R.v6, N.v6.
  rewrite ?node_20680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20682 (s : N.State) (i : N.Inputs) :
  R.v20682 (state s) (inputs i) = Zmod.unsigned (N.v20682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20682 s i)) at 1.
  unfold R.v20682, N.v20682.
  rewrite ?node_7196.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20683 (s : N.State) (i : N.Inputs) :
  R.v20683 (state s) (inputs i) = Zmod.unsigned (N.v20683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20683 s i)) at 1.
  unfold R.v20683, N.v20683.
  unfold R.v6, N.v6.
  rewrite ?node_7297.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20684 (s : N.State) (i : N.Inputs) :
  R.v20684 (state s) (inputs i) = Zmod.unsigned (N.v20684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20684 s i)) at 1.
  unfold R.v20684, N.v20684.
  unfold R.v6, N.v6.
  rewrite ?node_7331.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20685 (s : N.State) (i : N.Inputs) :
  R.v20685 (state s) (inputs i) = Zmod.unsigned (N.v20685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20685 s i)) at 1.
  unfold R.v20685, N.v20685.
  rewrite ?node_20682.
  rewrite ?node_20683.
  rewrite ?node_20684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20686 (s : N.State) (i : N.Inputs) :
  R.v20686 (state s) (inputs i) = Zmod.unsigned (N.v20686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20686 s i)) at 1.
  unfold R.v20686, N.v20686.
  rewrite ?node_20681.
  rewrite ?node_20685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20687 (s : N.State) (i : N.Inputs) :
  R.v20687 (state s) (inputs i) = Zmod.unsigned (N.v20687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20687 s i)) at 1.
  unfold R.v20687, N.v20687.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20688 (s : N.State) (i : N.Inputs) :
  R.v20688 (state s) (inputs i) = Zmod.unsigned (N.v20688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20688 s i)) at 1.
  unfold R.v20688, N.v20688.
  unfold R.v16463, N.v16463.
  rewrite !state_r474_nr_5F474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r474_nr_5F474 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20689 (s : N.State) (i : N.Inputs) :
  R.v20689 (state s) (inputs i) = Zmod.unsigned (N.v20689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20689 s i)) at 1.
  unfold R.v20689, N.v20689.
  unfold R.v6, N.v6.
  rewrite !state_r473_nr_5F473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r473_nr_5F473 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20690 (s : N.State) (i : N.Inputs) :
  R.v20690 (state s) (inputs i) = Zmod.unsigned (N.v20690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20690 s i)) at 1.
  unfold R.v20690, N.v20690.
  unfold R.v6, N.v6.
  rewrite !state_r472_nr_5F472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r472_nr_5F472 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20691 (s : N.State) (i : N.Inputs) :
  R.v20691 (state s) (inputs i) = Zmod.unsigned (N.v20691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20691 s i)) at 1.
  unfold R.v20691, N.v20691.
  rewrite ?node_20689.
  rewrite ?node_20690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20692 (s : N.State) (i : N.Inputs) :
  R.v20692 (state s) (inputs i) = Zmod.unsigned (N.v20692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20692 s i)) at 1.
  unfold R.v20692, N.v20692.
  unfold R.v16484, N.v16484.
  rewrite ?node_20691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20693 (s : N.State) (i : N.Inputs) :
  R.v20693 (state s) (inputs i) = Zmod.unsigned (N.v20693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20693 s i)) at 1.
  unfold R.v20693, N.v20693.
  rewrite ?node_20688.
  rewrite ?node_20692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20694 (s : N.State) (i : N.Inputs) :
  R.v20694 (state s) (inputs i) = Zmod.unsigned (N.v20694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20694 s i)) at 1.
  unfold R.v20694, N.v20694.
  unfold R.v6, N.v6.
  rewrite ?node_20693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20695 (s : N.State) (i : N.Inputs) :
  R.v20695 (state s) (inputs i) = Zmod.unsigned (N.v20695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20695 s i)) at 1.
  unfold R.v20695, N.v20695.
  rewrite ?node_7191.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20696 (s : N.State) (i : N.Inputs) :
  R.v20696 (state s) (inputs i) = Zmod.unsigned (N.v20696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20696 s i)) at 1.
  unfold R.v20696, N.v20696.
  unfold R.v6, N.v6.
  rewrite ?node_7297.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20697 (s : N.State) (i : N.Inputs) :
  R.v20697 (state s) (inputs i) = Zmod.unsigned (N.v20697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20697 s i)) at 1.
  unfold R.v20697, N.v20697.
  rewrite ?node_20695.
  rewrite ?node_20696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20698 (s : N.State) (i : N.Inputs) :
  R.v20698 (state s) (inputs i) = Zmod.unsigned (N.v20698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20698 s i)) at 1.
  unfold R.v20698, N.v20698.
  rewrite ?node_20694.
  rewrite ?node_20697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20699 (s : N.State) (i : N.Inputs) :
  R.v20699 (state s) (inputs i) = Zmod.unsigned (N.v20699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20699 s i)) at 1.
  unfold R.v20699, N.v20699.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20700 (s : N.State) (i : N.Inputs) :
  R.v20700 (state s) (inputs i) = Zmod.unsigned (N.v20700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20700 s i)) at 1.
  unfold R.v20700, N.v20700.
  rewrite ?node_7195.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20701 (s : N.State) (i : N.Inputs) :
  R.v20701 (state s) (inputs i) = Zmod.unsigned (N.v20701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20701 s i)) at 1.
  unfold R.v20701, N.v20701.
  unfold R.v6, N.v6.
  rewrite !state_r475_nr_5F475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r475_nr_5F475 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20702 (s : N.State) (i : N.Inputs) :
  R.v20702 (state s) (inputs i) = Zmod.unsigned (N.v20702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20702 s i)) at 1.
  unfold R.v20702, N.v20702.
  unfold R.v6, N.v6.
  rewrite ?node_7191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20703 (s : N.State) (i : N.Inputs) :
  R.v20703 (state s) (inputs i) = Zmod.unsigned (N.v20703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20703 s i)) at 1.
  unfold R.v20703, N.v20703.
  rewrite ?node_20701.
  rewrite ?node_20702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20704 (s : N.State) (i : N.Inputs) :
  R.v20704 (state s) (inputs i) = Zmod.unsigned (N.v20704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20704 s i)) at 1.
  unfold R.v20704, N.v20704.
  unfold R.v16484, N.v16484.
  rewrite ?node_20703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20705 (s : N.State) (i : N.Inputs) :
  R.v20705 (state s) (inputs i) = Zmod.unsigned (N.v20705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20705 s i)) at 1.
  unfold R.v20705, N.v20705.
  rewrite ?node_20700.
  rewrite ?node_20704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20706 (s : N.State) (i : N.Inputs) :
  R.v20706 (state s) (inputs i) = Zmod.unsigned (N.v20706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20706 s i)) at 1.
  unfold R.v20706, N.v20706.
  unfold R.v6, N.v6.
  rewrite ?node_20705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20707 (s : N.State) (i : N.Inputs) :
  R.v20707 (state s) (inputs i) = Zmod.unsigned (N.v20707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20707 s i)) at 1.
  unfold R.v20707, N.v20707.
  rewrite ?node_7196.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20708 (s : N.State) (i : N.Inputs) :
  R.v20708 (state s) (inputs i) = Zmod.unsigned (N.v20708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20708 s i)) at 1.
  unfold R.v20708, N.v20708.
  unfold R.v6, N.v6.
  rewrite ?node_7331.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20709 (s : N.State) (i : N.Inputs) :
  R.v20709 (state s) (inputs i) = Zmod.unsigned (N.v20709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20709 s i)) at 1.
  unfold R.v20709, N.v20709.
  rewrite ?node_20707.
  rewrite ?node_20708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20710 (s : N.State) (i : N.Inputs) :
  R.v20710 (state s) (inputs i) = Zmod.unsigned (N.v20710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20710 s i)) at 1.
  unfold R.v20710, N.v20710.
  rewrite ?node_20706.
  rewrite ?node_20709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20711 (s : N.State) (i : N.Inputs) :
  R.v20711 (state s) (inputs i) = Zmod.unsigned (N.v20711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20711 s i)) at 1.
  unfold R.v20711, N.v20711.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20712 (s : N.State) (i : N.Inputs) :
  R.v20712 (state s) (inputs i) = Zmod.unsigned (N.v20712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20712 s i)) at 1.
  unfold R.v20712, N.v20712.
  rewrite ?node_7207.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20713 (s : N.State) (i : N.Inputs) :
  R.v20713 (state s) (inputs i) = Zmod.unsigned (N.v20713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20713 s i)) at 1.
  unfold R.v20713, N.v20713.
  unfold R.v16463, N.v16463.
  rewrite !state_r479_nr_5F479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r479_nr_5F479 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20714 (s : N.State) (i : N.Inputs) :
  R.v20714 (state s) (inputs i) = Zmod.unsigned (N.v20714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20714 s i)) at 1.
  unfold R.v20714, N.v20714.
  unfold R.v16463, N.v16463.
  rewrite !state_r478_nr_5F478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r478_nr_5F478 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20715 (s : N.State) (i : N.Inputs) :
  R.v20715 (state s) (inputs i) = Zmod.unsigned (N.v20715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20715 s i)) at 1.
  unfold R.v20715, N.v20715.
  unfold R.v6, N.v6.
  rewrite !state_r477_nr_5F477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r477_nr_5F477 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20716 (s : N.State) (i : N.Inputs) :
  R.v20716 (state s) (inputs i) = Zmod.unsigned (N.v20716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20716 s i)) at 1.
  unfold R.v20716, N.v20716.
  unfold R.v6, N.v6.
  rewrite !state_r476_nr_5F476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r476_nr_5F476 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20717 (s : N.State) (i : N.Inputs) :
  R.v20717 (state s) (inputs i) = Zmod.unsigned (N.v20717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20717 s i)) at 1.
  unfold R.v20717, N.v20717.
  rewrite ?node_20715.
  rewrite ?node_20716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20718 (s : N.State) (i : N.Inputs) :
  R.v20718 (state s) (inputs i) = Zmod.unsigned (N.v20718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20718 s i)) at 1.
  unfold R.v20718, N.v20718.
  unfold R.v16484, N.v16484.
  rewrite ?node_20717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20719 (s : N.State) (i : N.Inputs) :
  R.v20719 (state s) (inputs i) = Zmod.unsigned (N.v20719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20719 s i)) at 1.
  unfold R.v20719, N.v20719.
  rewrite ?node_20712.
  rewrite ?node_20713.
  rewrite ?node_20714.
  rewrite ?node_20718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20720 (s : N.State) (i : N.Inputs) :
  R.v20720 (state s) (inputs i) = Zmod.unsigned (N.v20720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20720 s i)) at 1.
  unfold R.v20720, N.v20720.
  unfold R.v6, N.v6.
  rewrite ?node_20719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20721 (s : N.State) (i : N.Inputs) :
  R.v20721 (state s) (inputs i) = Zmod.unsigned (N.v20721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20721 s i)) at 1.
  unfold R.v20721, N.v20721.
  rewrite ?node_7208.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20722 (s : N.State) (i : N.Inputs) :
  R.v20722 (state s) (inputs i) = Zmod.unsigned (N.v20722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20722 s i)) at 1.
  unfold R.v20722, N.v20722.
  unfold R.v6, N.v6.
  rewrite ?node_7309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20723 (s : N.State) (i : N.Inputs) :
  R.v20723 (state s) (inputs i) = Zmod.unsigned (N.v20723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20723 s i)) at 1.
  unfold R.v20723, N.v20723.
  unfold R.v6, N.v6.
  rewrite ?node_7335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20724 (s : N.State) (i : N.Inputs) :
  R.v20724 (state s) (inputs i) = Zmod.unsigned (N.v20724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20724 s i)) at 1.
  unfold R.v20724, N.v20724.
  rewrite ?node_20721.
  rewrite ?node_20722.
  rewrite ?node_20723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20725 (s : N.State) (i : N.Inputs) :
  R.v20725 (state s) (inputs i) = Zmod.unsigned (N.v20725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20725 s i)) at 1.
  unfold R.v20725, N.v20725.
  rewrite ?node_20720.
  rewrite ?node_20724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20726 (s : N.State) (i : N.Inputs) :
  R.v20726 (state s) (inputs i) = Zmod.unsigned (N.v20726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20726 s i)) at 1.
  unfold R.v20726, N.v20726.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20727 (s : N.State) (i : N.Inputs) :
  R.v20727 (state s) (inputs i) = Zmod.unsigned (N.v20727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20727 s i)) at 1.
  unfold R.v20727, N.v20727.
  unfold R.v16463, N.v16463.
  rewrite !state_r478_nr_5F478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r478_nr_5F478 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20728 (s : N.State) (i : N.Inputs) :
  R.v20728 (state s) (inputs i) = Zmod.unsigned (N.v20728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20728 s i)) at 1.
  unfold R.v20728, N.v20728.
  unfold R.v6, N.v6.
  rewrite !state_r477_nr_5F477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r477_nr_5F477 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20729 (s : N.State) (i : N.Inputs) :
  R.v20729 (state s) (inputs i) = Zmod.unsigned (N.v20729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20729 s i)) at 1.
  unfold R.v20729, N.v20729.
  unfold R.v6, N.v6.
  rewrite !state_r476_nr_5F476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r476_nr_5F476 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20730 (s : N.State) (i : N.Inputs) :
  R.v20730 (state s) (inputs i) = Zmod.unsigned (N.v20730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20730 s i)) at 1.
  unfold R.v20730, N.v20730.
  rewrite ?node_20728.
  rewrite ?node_20729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20731 (s : N.State) (i : N.Inputs) :
  R.v20731 (state s) (inputs i) = Zmod.unsigned (N.v20731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20731 s i)) at 1.
  unfold R.v20731, N.v20731.
  unfold R.v16484, N.v16484.
  rewrite ?node_20730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20732 (s : N.State) (i : N.Inputs) :
  R.v20732 (state s) (inputs i) = Zmod.unsigned (N.v20732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20732 s i)) at 1.
  unfold R.v20732, N.v20732.
  rewrite ?node_20727.
  rewrite ?node_20731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20733 (s : N.State) (i : N.Inputs) :
  R.v20733 (state s) (inputs i) = Zmod.unsigned (N.v20733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20733 s i)) at 1.
  unfold R.v20733, N.v20733.
  unfold R.v6, N.v6.
  rewrite ?node_20732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20734 (s : N.State) (i : N.Inputs) :
  R.v20734 (state s) (inputs i) = Zmod.unsigned (N.v20734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20734 s i)) at 1.
  unfold R.v20734, N.v20734.
  rewrite ?node_7203.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20735 (s : N.State) (i : N.Inputs) :
  R.v20735 (state s) (inputs i) = Zmod.unsigned (N.v20735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20735 s i)) at 1.
  unfold R.v20735, N.v20735.
  unfold R.v6, N.v6.
  rewrite ?node_7309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20736 (s : N.State) (i : N.Inputs) :
  R.v20736 (state s) (inputs i) = Zmod.unsigned (N.v20736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20736 s i)) at 1.
  unfold R.v20736, N.v20736.
  rewrite ?node_20734.
  rewrite ?node_20735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20737 (s : N.State) (i : N.Inputs) :
  R.v20737 (state s) (inputs i) = Zmod.unsigned (N.v20737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20737 s i)) at 1.
  unfold R.v20737, N.v20737.
  rewrite ?node_20733.
  rewrite ?node_20736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20738 (s : N.State) (i : N.Inputs) :
  R.v20738 (state s) (inputs i) = Zmod.unsigned (N.v20738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20738 s i)) at 1.
  unfold R.v20738, N.v20738.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20739 (s : N.State) (i : N.Inputs) :
  R.v20739 (state s) (inputs i) = Zmod.unsigned (N.v20739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20739 s i)) at 1.
  unfold R.v20739, N.v20739.
  rewrite ?node_7207.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20740 (s : N.State) (i : N.Inputs) :
  R.v20740 (state s) (inputs i) = Zmod.unsigned (N.v20740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20740 s i)) at 1.
  unfold R.v20740, N.v20740.
  unfold R.v6, N.v6.
  rewrite !state_r479_nr_5F479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r479_nr_5F479 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20741 (s : N.State) (i : N.Inputs) :
  R.v20741 (state s) (inputs i) = Zmod.unsigned (N.v20741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20741 s i)) at 1.
  unfold R.v20741, N.v20741.
  unfold R.v6, N.v6.
  rewrite ?node_7203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20742 (s : N.State) (i : N.Inputs) :
  R.v20742 (state s) (inputs i) = Zmod.unsigned (N.v20742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20742 s i)) at 1.
  unfold R.v20742, N.v20742.
  rewrite ?node_20740.
  rewrite ?node_20741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20743 (s : N.State) (i : N.Inputs) :
  R.v20743 (state s) (inputs i) = Zmod.unsigned (N.v20743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20743 s i)) at 1.
  unfold R.v20743, N.v20743.
  unfold R.v16484, N.v16484.
  rewrite ?node_20742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20744 (s : N.State) (i : N.Inputs) :
  R.v20744 (state s) (inputs i) = Zmod.unsigned (N.v20744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20744 s i)) at 1.
  unfold R.v20744, N.v20744.
  rewrite ?node_20739.
  rewrite ?node_20743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20745 (s : N.State) (i : N.Inputs) :
  R.v20745 (state s) (inputs i) = Zmod.unsigned (N.v20745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20745 s i)) at 1.
  unfold R.v20745, N.v20745.
  unfold R.v6, N.v6.
  rewrite ?node_20744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20746 (s : N.State) (i : N.Inputs) :
  R.v20746 (state s) (inputs i) = Zmod.unsigned (N.v20746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20746 s i)) at 1.
  unfold R.v20746, N.v20746.
  rewrite ?node_7208.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20747 (s : N.State) (i : N.Inputs) :
  R.v20747 (state s) (inputs i) = Zmod.unsigned (N.v20747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20747 s i)) at 1.
  unfold R.v20747, N.v20747.
  unfold R.v6, N.v6.
  rewrite ?node_7335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20748 (s : N.State) (i : N.Inputs) :
  R.v20748 (state s) (inputs i) = Zmod.unsigned (N.v20748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20748 s i)) at 1.
  unfold R.v20748, N.v20748.
  rewrite ?node_20746.
  rewrite ?node_20747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20749 (s : N.State) (i : N.Inputs) :
  R.v20749 (state s) (inputs i) = Zmod.unsigned (N.v20749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20749 s i)) at 1.
  unfold R.v20749, N.v20749.
  rewrite ?node_20745.
  rewrite ?node_20748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20750 (s : N.State) (i : N.Inputs) :
  R.v20750 (state s) (inputs i) = Zmod.unsigned (N.v20750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20750 s i)) at 1.
  unfold R.v20750, N.v20750.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20751 (s : N.State) (i : N.Inputs) :
  R.v20751 (state s) (inputs i) = Zmod.unsigned (N.v20751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20751 s i)) at 1.
  unfold R.v20751, N.v20751.
  unfold R.v6, N.v6.
  rewrite !state_r481_nr_5F481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r481_nr_5F481 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20752 (s : N.State) (i : N.Inputs) :
  R.v20752 (state s) (inputs i) = Zmod.unsigned (N.v20752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20752 s i)) at 1.
  unfold R.v20752, N.v20752.
  unfold R.v6, N.v6.
  rewrite !state_r480_nr_5F480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r480_nr_5F480 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20753 (s : N.State) (i : N.Inputs) :
  R.v20753 (state s) (inputs i) = Zmod.unsigned (N.v20753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20753 s i)) at 1.
  unfold R.v20753, N.v20753.
  rewrite ?node_20751.
  rewrite ?node_20752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20754 (s : N.State) (i : N.Inputs) :
  R.v20754 (state s) (inputs i) = Zmod.unsigned (N.v20754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20754 s i)) at 1.
  unfold R.v20754, N.v20754.
  unfold R.v16463, N.v16463.
  rewrite ?node_20753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20755 (s : N.State) (i : N.Inputs) :
  R.v20755 (state s) (inputs i) = Zmod.unsigned (N.v20755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20755 s i)) at 1.
  unfold R.v20755, N.v20755.
  rewrite ?node_7209.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20756 (s : N.State) (i : N.Inputs) :
  R.v20756 (state s) (inputs i) = Zmod.unsigned (N.v20756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20756 s i)) at 1.
  unfold R.v20756, N.v20756.
  unfold R.v6, N.v6.
  rewrite ?node_7337.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20757 (s : N.State) (i : N.Inputs) :
  R.v20757 (state s) (inputs i) = Zmod.unsigned (N.v20757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20757 s i)) at 1.
  unfold R.v20757, N.v20757.
  rewrite ?node_20755.
  rewrite ?node_20756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20758 (s : N.State) (i : N.Inputs) :
  R.v20758 (state s) (inputs i) = Zmod.unsigned (N.v20758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20758 s i)) at 1.
  unfold R.v20758, N.v20758.
  rewrite ?node_20754.
  rewrite ?node_20757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20759 (s : N.State) (i : N.Inputs) :
  R.v20759 (state s) (inputs i) = Zmod.unsigned (N.v20759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20759 s i)) at 1.
  unfold R.v20759, N.v20759.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20760 (s : N.State) (i : N.Inputs) :
  R.v20760 (state s) (inputs i) = Zmod.unsigned (N.v20760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20760 s i)) at 1.
  unfold R.v20760, N.v20760.
  rewrite ?node_7274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20761 (s : N.State) (i : N.Inputs) :
  R.v20761 (state s) (inputs i) = Zmod.unsigned (N.v20761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20761 s i)) at 1.
  unfold R.v20761, N.v20761.
  unfold R.v16463, N.v16463.
  rewrite !state_r485_nr_5F485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r485_nr_5F485 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20762 (s : N.State) (i : N.Inputs) :
  R.v20762 (state s) (inputs i) = Zmod.unsigned (N.v20762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20762 s i)) at 1.
  unfold R.v20762, N.v20762.
  unfold R.v16463, N.v16463.
  rewrite !state_r484_nr_5F484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r484_nr_5F484 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20763 (s : N.State) (i : N.Inputs) :
  R.v20763 (state s) (inputs i) = Zmod.unsigned (N.v20763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20763 s i)) at 1.
  unfold R.v20763, N.v20763.
  unfold R.v6, N.v6.
  rewrite !state_r483_nr_5F483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r483_nr_5F483 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20764 (s : N.State) (i : N.Inputs) :
  R.v20764 (state s) (inputs i) = Zmod.unsigned (N.v20764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20764 s i)) at 1.
  unfold R.v20764, N.v20764.
  unfold R.v6, N.v6.
  rewrite !state_r482_nr_5F482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r482_nr_5F482 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20765 (s : N.State) (i : N.Inputs) :
  R.v20765 (state s) (inputs i) = Zmod.unsigned (N.v20765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20765 s i)) at 1.
  unfold R.v20765, N.v20765.
  rewrite ?node_20763.
  rewrite ?node_20764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20766 (s : N.State) (i : N.Inputs) :
  R.v20766 (state s) (inputs i) = Zmod.unsigned (N.v20766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20766 s i)) at 1.
  unfold R.v20766, N.v20766.
  unfold R.v16484, N.v16484.
  rewrite ?node_20765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20767 (s : N.State) (i : N.Inputs) :
  R.v20767 (state s) (inputs i) = Zmod.unsigned (N.v20767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20767 s i)) at 1.
  unfold R.v20767, N.v20767.
  rewrite ?node_20760.
  rewrite ?node_20761.
  rewrite ?node_20762.
  rewrite ?node_20766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20768 (s : N.State) (i : N.Inputs) :
  R.v20768 (state s) (inputs i) = Zmod.unsigned (N.v20768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20768 s i)) at 1.
  unfold R.v20768, N.v20768.
  unfold R.v6, N.v6.
  rewrite ?node_20767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20769 (s : N.State) (i : N.Inputs) :
  R.v20769 (state s) (inputs i) = Zmod.unsigned (N.v20769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20769 s i)) at 1.
  unfold R.v20769, N.v20769.
  rewrite ?node_7275.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20770 (s : N.State) (i : N.Inputs) :
  R.v20770 (state s) (inputs i) = Zmod.unsigned (N.v20770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20770 s i)) at 1.
  unfold R.v20770, N.v20770.
  unfold R.v6, N.v6.
  rewrite ?node_7378.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20771 (s : N.State) (i : N.Inputs) :
  R.v20771 (state s) (inputs i) = Zmod.unsigned (N.v20771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20771 s i)) at 1.
  unfold R.v20771, N.v20771.
  unfold R.v6, N.v6.
  rewrite ?node_7420.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20772 (s : N.State) (i : N.Inputs) :
  R.v20772 (state s) (inputs i) = Zmod.unsigned (N.v20772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20772 s i)) at 1.
  unfold R.v20772, N.v20772.
  rewrite ?node_20769.
  rewrite ?node_20770.
  rewrite ?node_20771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20773 (s : N.State) (i : N.Inputs) :
  R.v20773 (state s) (inputs i) = Zmod.unsigned (N.v20773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20773 s i)) at 1.
  unfold R.v20773, N.v20773.
  rewrite ?node_20768.
  rewrite ?node_20772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20774 (s : N.State) (i : N.Inputs) :
  R.v20774 (state s) (inputs i) = Zmod.unsigned (N.v20774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20774 s i)) at 1.
  unfold R.v20774, N.v20774.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20775 (s : N.State) (i : N.Inputs) :
  R.v20775 (state s) (inputs i) = Zmod.unsigned (N.v20775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20775 s i)) at 1.
  unfold R.v20775, N.v20775.
  unfold R.v16463, N.v16463.
  rewrite !state_r484_nr_5F484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r484_nr_5F484 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20776 (s : N.State) (i : N.Inputs) :
  R.v20776 (state s) (inputs i) = Zmod.unsigned (N.v20776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20776 s i)) at 1.
  unfold R.v20776, N.v20776.
  unfold R.v6, N.v6.
  rewrite !state_r483_nr_5F483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r483_nr_5F483 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20777 (s : N.State) (i : N.Inputs) :
  R.v20777 (state s) (inputs i) = Zmod.unsigned (N.v20777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20777 s i)) at 1.
  unfold R.v20777, N.v20777.
  unfold R.v6, N.v6.
  rewrite !state_r482_nr_5F482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r482_nr_5F482 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20778 (s : N.State) (i : N.Inputs) :
  R.v20778 (state s) (inputs i) = Zmod.unsigned (N.v20778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20778 s i)) at 1.
  unfold R.v20778, N.v20778.
  rewrite ?node_20776.
  rewrite ?node_20777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20779 (s : N.State) (i : N.Inputs) :
  R.v20779 (state s) (inputs i) = Zmod.unsigned (N.v20779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20779 s i)) at 1.
  unfold R.v20779, N.v20779.
  unfold R.v16484, N.v16484.
  rewrite ?node_20778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20780 (s : N.State) (i : N.Inputs) :
  R.v20780 (state s) (inputs i) = Zmod.unsigned (N.v20780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20780 s i)) at 1.
  unfold R.v20780, N.v20780.
  rewrite ?node_20775.
  rewrite ?node_20779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20781 (s : N.State) (i : N.Inputs) :
  R.v20781 (state s) (inputs i) = Zmod.unsigned (N.v20781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20781 s i)) at 1.
  unfold R.v20781, N.v20781.
  unfold R.v6, N.v6.
  rewrite ?node_20780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20782 (s : N.State) (i : N.Inputs) :
  R.v20782 (state s) (inputs i) = Zmod.unsigned (N.v20782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20782 s i)) at 1.
  unfold R.v20782, N.v20782.
  rewrite ?node_7270.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20783 (s : N.State) (i : N.Inputs) :
  R.v20783 (state s) (inputs i) = Zmod.unsigned (N.v20783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20783 s i)) at 1.
  unfold R.v20783, N.v20783.
  unfold R.v6, N.v6.
  rewrite ?node_7378.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20784 (s : N.State) (i : N.Inputs) :
  R.v20784 (state s) (inputs i) = Zmod.unsigned (N.v20784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20784 s i)) at 1.
  unfold R.v20784, N.v20784.
  rewrite ?node_20782.
  rewrite ?node_20783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20785 (s : N.State) (i : N.Inputs) :
  R.v20785 (state s) (inputs i) = Zmod.unsigned (N.v20785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20785 s i)) at 1.
  unfold R.v20785, N.v20785.
  rewrite ?node_20781.
  rewrite ?node_20784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20786 (s : N.State) (i : N.Inputs) :
  R.v20786 (state s) (inputs i) = Zmod.unsigned (N.v20786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20786 s i)) at 1.
  unfold R.v20786, N.v20786.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20787 (s : N.State) (i : N.Inputs) :
  R.v20787 (state s) (inputs i) = Zmod.unsigned (N.v20787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20787 s i)) at 1.
  unfold R.v20787, N.v20787.
  rewrite ?node_7274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20788 (s : N.State) (i : N.Inputs) :
  R.v20788 (state s) (inputs i) = Zmod.unsigned (N.v20788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20788 s i)) at 1.
  unfold R.v20788, N.v20788.
  unfold R.v6, N.v6.
  rewrite !state_r485_nr_5F485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r485_nr_5F485 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20789 (s : N.State) (i : N.Inputs) :
  R.v20789 (state s) (inputs i) = Zmod.unsigned (N.v20789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20789 s i)) at 1.
  unfold R.v20789, N.v20789.
  unfold R.v6, N.v6.
  rewrite ?node_7270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20790 (s : N.State) (i : N.Inputs) :
  R.v20790 (state s) (inputs i) = Zmod.unsigned (N.v20790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20790 s i)) at 1.
  unfold R.v20790, N.v20790.
  rewrite ?node_20788.
  rewrite ?node_20789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20791 (s : N.State) (i : N.Inputs) :
  R.v20791 (state s) (inputs i) = Zmod.unsigned (N.v20791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20791 s i)) at 1.
  unfold R.v20791, N.v20791.
  unfold R.v16484, N.v16484.
  rewrite ?node_20790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20792 (s : N.State) (i : N.Inputs) :
  R.v20792 (state s) (inputs i) = Zmod.unsigned (N.v20792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20792 s i)) at 1.
  unfold R.v20792, N.v20792.
  rewrite ?node_20787.
  rewrite ?node_20791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20793 (s : N.State) (i : N.Inputs) :
  R.v20793 (state s) (inputs i) = Zmod.unsigned (N.v20793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20793 s i)) at 1.
  unfold R.v20793, N.v20793.
  unfold R.v6, N.v6.
  rewrite ?node_20792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20794 (s : N.State) (i : N.Inputs) :
  R.v20794 (state s) (inputs i) = Zmod.unsigned (N.v20794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20794 s i)) at 1.
  unfold R.v20794, N.v20794.
  rewrite ?node_7275.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20795 (s : N.State) (i : N.Inputs) :
  R.v20795 (state s) (inputs i) = Zmod.unsigned (N.v20795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20795 s i)) at 1.
  unfold R.v20795, N.v20795.
  unfold R.v6, N.v6.
  rewrite ?node_7420.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20796 (s : N.State) (i : N.Inputs) :
  R.v20796 (state s) (inputs i) = Zmod.unsigned (N.v20796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20796 s i)) at 1.
  unfold R.v20796, N.v20796.
  rewrite ?node_20794.
  rewrite ?node_20795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20797 (s : N.State) (i : N.Inputs) :
  R.v20797 (state s) (inputs i) = Zmod.unsigned (N.v20797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20797 s i)) at 1.
  unfold R.v20797, N.v20797.
  rewrite ?node_20793.
  rewrite ?node_20796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20798 (s : N.State) (i : N.Inputs) :
  R.v20798 (state s) (inputs i) = Zmod.unsigned (N.v20798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20798 s i)) at 1.
  unfold R.v20798, N.v20798.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20799 (s : N.State) (i : N.Inputs) :
  R.v20799 (state s) (inputs i) = Zmod.unsigned (N.v20799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20799 s i)) at 1.
  unfold R.v20799, N.v20799.
  rewrite ?node_7281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20800 (s : N.State) (i : N.Inputs) :
  R.v20800 (state s) (inputs i) = Zmod.unsigned (N.v20800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20800 s i)) at 1.
  unfold R.v20800, N.v20800.
  unfold R.v16463, N.v16463.
  rewrite !state_r489_nr_5F489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r489_nr_5F489 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20801 (s : N.State) (i : N.Inputs) :
  R.v20801 (state s) (inputs i) = Zmod.unsigned (N.v20801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20801 s i)) at 1.
  unfold R.v20801, N.v20801.
  unfold R.v16463, N.v16463.
  rewrite !state_r488_nr_5F488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r488_nr_5F488 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20802 (s : N.State) (i : N.Inputs) :
  R.v20802 (state s) (inputs i) = Zmod.unsigned (N.v20802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20802 s i)) at 1.
  unfold R.v20802, N.v20802.
  unfold R.v6, N.v6.
  rewrite !state_r487_nr_5F487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r487_nr_5F487 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20803 (s : N.State) (i : N.Inputs) :
  R.v20803 (state s) (inputs i) = Zmod.unsigned (N.v20803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20803 s i)) at 1.
  unfold R.v20803, N.v20803.
  unfold R.v6, N.v6.
  rewrite !state_r486_nr_5F486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r486_nr_5F486 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20804 (s : N.State) (i : N.Inputs) :
  R.v20804 (state s) (inputs i) = Zmod.unsigned (N.v20804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20804 s i)) at 1.
  unfold R.v20804, N.v20804.
  rewrite ?node_20802.
  rewrite ?node_20803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20805 (s : N.State) (i : N.Inputs) :
  R.v20805 (state s) (inputs i) = Zmod.unsigned (N.v20805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20805 s i)) at 1.
  unfold R.v20805, N.v20805.
  unfold R.v16484, N.v16484.
  rewrite ?node_20804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20806 (s : N.State) (i : N.Inputs) :
  R.v20806 (state s) (inputs i) = Zmod.unsigned (N.v20806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20806 s i)) at 1.
  unfold R.v20806, N.v20806.
  rewrite ?node_20799.
  rewrite ?node_20800.
  rewrite ?node_20801.
  rewrite ?node_20805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20807 (s : N.State) (i : N.Inputs) :
  R.v20807 (state s) (inputs i) = Zmod.unsigned (N.v20807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20807 s i)) at 1.
  unfold R.v20807, N.v20807.
  unfold R.v6, N.v6.
  rewrite ?node_20806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20808 (s : N.State) (i : N.Inputs) :
  R.v20808 (state s) (inputs i) = Zmod.unsigned (N.v20808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20808 s i)) at 1.
  unfold R.v20808, N.v20808.
  rewrite ?node_7282.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20809 (s : N.State) (i : N.Inputs) :
  R.v20809 (state s) (inputs i) = Zmod.unsigned (N.v20809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20809 s i)) at 1.
  unfold R.v20809, N.v20809.
  unfold R.v6, N.v6.
  rewrite ?node_7385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20810 (s : N.State) (i : N.Inputs) :
  R.v20810 (state s) (inputs i) = Zmod.unsigned (N.v20810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20810 s i)) at 1.
  unfold R.v20810, N.v20810.
  unfold R.v6, N.v6.
  rewrite ?node_7424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20811 (s : N.State) (i : N.Inputs) :
  R.v20811 (state s) (inputs i) = Zmod.unsigned (N.v20811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20811 s i)) at 1.
  unfold R.v20811, N.v20811.
  rewrite ?node_20808.
  rewrite ?node_20809.
  rewrite ?node_20810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20812 (s : N.State) (i : N.Inputs) :
  R.v20812 (state s) (inputs i) = Zmod.unsigned (N.v20812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20812 s i)) at 1.
  unfold R.v20812, N.v20812.
  rewrite ?node_20807.
  rewrite ?node_20811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20813 (s : N.State) (i : N.Inputs) :
  R.v20813 (state s) (inputs i) = Zmod.unsigned (N.v20813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20813 s i)) at 1.
  unfold R.v20813, N.v20813.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20814 (s : N.State) (i : N.Inputs) :
  R.v20814 (state s) (inputs i) = Zmod.unsigned (N.v20814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20814 s i)) at 1.
  unfold R.v20814, N.v20814.
  unfold R.v16463, N.v16463.
  rewrite !state_r488_nr_5F488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r488_nr_5F488 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20815 (s : N.State) (i : N.Inputs) :
  R.v20815 (state s) (inputs i) = Zmod.unsigned (N.v20815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20815 s i)) at 1.
  unfold R.v20815, N.v20815.
  unfold R.v6, N.v6.
  rewrite !state_r487_nr_5F487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r487_nr_5F487 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20816 (s : N.State) (i : N.Inputs) :
  R.v20816 (state s) (inputs i) = Zmod.unsigned (N.v20816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20816 s i)) at 1.
  unfold R.v20816, N.v20816.
  unfold R.v6, N.v6.
  rewrite !state_r486_nr_5F486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r486_nr_5F486 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20817 (s : N.State) (i : N.Inputs) :
  R.v20817 (state s) (inputs i) = Zmod.unsigned (N.v20817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20817 s i)) at 1.
  unfold R.v20817, N.v20817.
  rewrite ?node_20815.
  rewrite ?node_20816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20818 (s : N.State) (i : N.Inputs) :
  R.v20818 (state s) (inputs i) = Zmod.unsigned (N.v20818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20818 s i)) at 1.
  unfold R.v20818, N.v20818.
  unfold R.v16484, N.v16484.
  rewrite ?node_20817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20819 (s : N.State) (i : N.Inputs) :
  R.v20819 (state s) (inputs i) = Zmod.unsigned (N.v20819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20819 s i)) at 1.
  unfold R.v20819, N.v20819.
  rewrite ?node_20814.
  rewrite ?node_20818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20820 (s : N.State) (i : N.Inputs) :
  R.v20820 (state s) (inputs i) = Zmod.unsigned (N.v20820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20820 s i)) at 1.
  unfold R.v20820, N.v20820.
  unfold R.v6, N.v6.
  rewrite ?node_20819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20821 (s : N.State) (i : N.Inputs) :
  R.v20821 (state s) (inputs i) = Zmod.unsigned (N.v20821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20821 s i)) at 1.
  unfold R.v20821, N.v20821.
  rewrite ?node_7277.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20822 (s : N.State) (i : N.Inputs) :
  R.v20822 (state s) (inputs i) = Zmod.unsigned (N.v20822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20822 s i)) at 1.
  unfold R.v20822, N.v20822.
  unfold R.v6, N.v6.
  rewrite ?node_7385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20823 (s : N.State) (i : N.Inputs) :
  R.v20823 (state s) (inputs i) = Zmod.unsigned (N.v20823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20823 s i)) at 1.
  unfold R.v20823, N.v20823.
  rewrite ?node_20821.
  rewrite ?node_20822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20824 (s : N.State) (i : N.Inputs) :
  R.v20824 (state s) (inputs i) = Zmod.unsigned (N.v20824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20824 s i)) at 1.
  unfold R.v20824, N.v20824.
  rewrite ?node_20820.
  rewrite ?node_20823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20825 (s : N.State) (i : N.Inputs) :
  R.v20825 (state s) (inputs i) = Zmod.unsigned (N.v20825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20825 s i)) at 1.
  unfold R.v20825, N.v20825.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20826 (s : N.State) (i : N.Inputs) :
  R.v20826 (state s) (inputs i) = Zmod.unsigned (N.v20826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20826 s i)) at 1.
  unfold R.v20826, N.v20826.
  rewrite ?node_7281.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20827 (s : N.State) (i : N.Inputs) :
  R.v20827 (state s) (inputs i) = Zmod.unsigned (N.v20827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20827 s i)) at 1.
  unfold R.v20827, N.v20827.
  unfold R.v6, N.v6.
  rewrite !state_r489_nr_5F489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r489_nr_5F489 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20828 (s : N.State) (i : N.Inputs) :
  R.v20828 (state s) (inputs i) = Zmod.unsigned (N.v20828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20828 s i)) at 1.
  unfold R.v20828, N.v20828.
  unfold R.v6, N.v6.
  rewrite ?node_7277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20829 (s : N.State) (i : N.Inputs) :
  R.v20829 (state s) (inputs i) = Zmod.unsigned (N.v20829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20829 s i)) at 1.
  unfold R.v20829, N.v20829.
  rewrite ?node_20827.
  rewrite ?node_20828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20830 (s : N.State) (i : N.Inputs) :
  R.v20830 (state s) (inputs i) = Zmod.unsigned (N.v20830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20830 s i)) at 1.
  unfold R.v20830, N.v20830.
  unfold R.v16484, N.v16484.
  rewrite ?node_20829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20831 (s : N.State) (i : N.Inputs) :
  R.v20831 (state s) (inputs i) = Zmod.unsigned (N.v20831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20831 s i)) at 1.
  unfold R.v20831, N.v20831.
  rewrite ?node_20826.
  rewrite ?node_20830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20832 (s : N.State) (i : N.Inputs) :
  R.v20832 (state s) (inputs i) = Zmod.unsigned (N.v20832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20832 s i)) at 1.
  unfold R.v20832, N.v20832.
  unfold R.v6, N.v6.
  rewrite ?node_20831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20833 (s : N.State) (i : N.Inputs) :
  R.v20833 (state s) (inputs i) = Zmod.unsigned (N.v20833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20833 s i)) at 1.
  unfold R.v20833, N.v20833.
  rewrite ?node_7282.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20834 (s : N.State) (i : N.Inputs) :
  R.v20834 (state s) (inputs i) = Zmod.unsigned (N.v20834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20834 s i)) at 1.
  unfold R.v20834, N.v20834.
  unfold R.v6, N.v6.
  rewrite ?node_7424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20835 (s : N.State) (i : N.Inputs) :
  R.v20835 (state s) (inputs i) = Zmod.unsigned (N.v20835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20835 s i)) at 1.
  unfold R.v20835, N.v20835.
  rewrite ?node_20833.
  rewrite ?node_20834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20836 (s : N.State) (i : N.Inputs) :
  R.v20836 (state s) (inputs i) = Zmod.unsigned (N.v20836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20836 s i)) at 1.
  unfold R.v20836, N.v20836.
  rewrite ?node_20832.
  rewrite ?node_20835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20837 (s : N.State) (i : N.Inputs) :
  R.v20837 (state s) (inputs i) = Zmod.unsigned (N.v20837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20837 s i)) at 1.
  unfold R.v20837, N.v20837.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20838 (s : N.State) (i : N.Inputs) :
  R.v20838 (state s) (inputs i) = Zmod.unsigned (N.v20838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20838 s i)) at 1.
  unfold R.v20838, N.v20838.
  rewrite ?node_7289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20839 (s : N.State) (i : N.Inputs) :
  R.v20839 (state s) (inputs i) = Zmod.unsigned (N.v20839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20839 s i)) at 1.
  unfold R.v20839, N.v20839.
  unfold R.v16463, N.v16463.
  rewrite !state_r493_nr_5F493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r493_nr_5F493 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20840 (s : N.State) (i : N.Inputs) :
  R.v20840 (state s) (inputs i) = Zmod.unsigned (N.v20840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20840 s i)) at 1.
  unfold R.v20840, N.v20840.
  unfold R.v16463, N.v16463.
  rewrite !state_r492_nr_5F492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r492_nr_5F492 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20841 (s : N.State) (i : N.Inputs) :
  R.v20841 (state s) (inputs i) = Zmod.unsigned (N.v20841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20841 s i)) at 1.
  unfold R.v20841, N.v20841.
  unfold R.v6, N.v6.
  rewrite !state_r491_nr_5F491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r491_nr_5F491 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20842 (s : N.State) (i : N.Inputs) :
  R.v20842 (state s) (inputs i) = Zmod.unsigned (N.v20842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20842 s i)) at 1.
  unfold R.v20842, N.v20842.
  unfold R.v6, N.v6.
  rewrite !state_r490_nr_5F490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r490_nr_5F490 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20843 (s : N.State) (i : N.Inputs) :
  R.v20843 (state s) (inputs i) = Zmod.unsigned (N.v20843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20843 s i)) at 1.
  unfold R.v20843, N.v20843.
  rewrite ?node_20841.
  rewrite ?node_20842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20844 (s : N.State) (i : N.Inputs) :
  R.v20844 (state s) (inputs i) = Zmod.unsigned (N.v20844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20844 s i)) at 1.
  unfold R.v20844, N.v20844.
  unfold R.v16484, N.v16484.
  rewrite ?node_20843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20845 (s : N.State) (i : N.Inputs) :
  R.v20845 (state s) (inputs i) = Zmod.unsigned (N.v20845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20845 s i)) at 1.
  unfold R.v20845, N.v20845.
  rewrite ?node_20838.
  rewrite ?node_20839.
  rewrite ?node_20840.
  rewrite ?node_20844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20846 (s : N.State) (i : N.Inputs) :
  R.v20846 (state s) (inputs i) = Zmod.unsigned (N.v20846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20846 s i)) at 1.
  unfold R.v20846, N.v20846.
  unfold R.v6, N.v6.
  rewrite ?node_20845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20847 (s : N.State) (i : N.Inputs) :
  R.v20847 (state s) (inputs i) = Zmod.unsigned (N.v20847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20847 s i)) at 1.
  unfold R.v20847, N.v20847.
  rewrite ?node_7290.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20848 (s : N.State) (i : N.Inputs) :
  R.v20848 (state s) (inputs i) = Zmod.unsigned (N.v20848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20848 s i)) at 1.
  unfold R.v20848, N.v20848.
  unfold R.v6, N.v6.
  rewrite ?node_7393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20849 (s : N.State) (i : N.Inputs) :
  R.v20849 (state s) (inputs i) = Zmod.unsigned (N.v20849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20849 s i)) at 1.
  unfold R.v20849, N.v20849.
  unfold R.v6, N.v6.
  rewrite ?node_7433.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20850 (s : N.State) (i : N.Inputs) :
  R.v20850 (state s) (inputs i) = Zmod.unsigned (N.v20850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20850 s i)) at 1.
  unfold R.v20850, N.v20850.
  rewrite ?node_20847.
  rewrite ?node_20848.
  rewrite ?node_20849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20851 (s : N.State) (i : N.Inputs) :
  R.v20851 (state s) (inputs i) = Zmod.unsigned (N.v20851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20851 s i)) at 1.
  unfold R.v20851, N.v20851.
  rewrite ?node_20846.
  rewrite ?node_20850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20852 (s : N.State) (i : N.Inputs) :
  R.v20852 (state s) (inputs i) = Zmod.unsigned (N.v20852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20852 s i)) at 1.
  unfold R.v20852, N.v20852.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20853 (s : N.State) (i : N.Inputs) :
  R.v20853 (state s) (inputs i) = Zmod.unsigned (N.v20853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20853 s i)) at 1.
  unfold R.v20853, N.v20853.
  unfold R.v16463, N.v16463.
  rewrite !state_r492_nr_5F492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r492_nr_5F492 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20854 (s : N.State) (i : N.Inputs) :
  R.v20854 (state s) (inputs i) = Zmod.unsigned (N.v20854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20854 s i)) at 1.
  unfold R.v20854, N.v20854.
  unfold R.v6, N.v6.
  rewrite !state_r491_nr_5F491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r491_nr_5F491 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20855 (s : N.State) (i : N.Inputs) :
  R.v20855 (state s) (inputs i) = Zmod.unsigned (N.v20855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20855 s i)) at 1.
  unfold R.v20855, N.v20855.
  unfold R.v6, N.v6.
  rewrite !state_r490_nr_5F490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r490_nr_5F490 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20856 (s : N.State) (i : N.Inputs) :
  R.v20856 (state s) (inputs i) = Zmod.unsigned (N.v20856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20856 s i)) at 1.
  unfold R.v20856, N.v20856.
  rewrite ?node_20854.
  rewrite ?node_20855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20857 (s : N.State) (i : N.Inputs) :
  R.v20857 (state s) (inputs i) = Zmod.unsigned (N.v20857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20857 s i)) at 1.
  unfold R.v20857, N.v20857.
  unfold R.v16484, N.v16484.
  rewrite ?node_20856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20858 (s : N.State) (i : N.Inputs) :
  R.v20858 (state s) (inputs i) = Zmod.unsigned (N.v20858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20858 s i)) at 1.
  unfold R.v20858, N.v20858.
  rewrite ?node_20853.
  rewrite ?node_20857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20859 (s : N.State) (i : N.Inputs) :
  R.v20859 (state s) (inputs i) = Zmod.unsigned (N.v20859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20859 s i)) at 1.
  unfold R.v20859, N.v20859.
  unfold R.v6, N.v6.
  rewrite ?node_20858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20860 (s : N.State) (i : N.Inputs) :
  R.v20860 (state s) (inputs i) = Zmod.unsigned (N.v20860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20860 s i)) at 1.
  unfold R.v20860, N.v20860.
  rewrite ?node_7285.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20861 (s : N.State) (i : N.Inputs) :
  R.v20861 (state s) (inputs i) = Zmod.unsigned (N.v20861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20861 s i)) at 1.
  unfold R.v20861, N.v20861.
  unfold R.v6, N.v6.
  rewrite ?node_7393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20862 (s : N.State) (i : N.Inputs) :
  R.v20862 (state s) (inputs i) = Zmod.unsigned (N.v20862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20862 s i)) at 1.
  unfold R.v20862, N.v20862.
  rewrite ?node_20860.
  rewrite ?node_20861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20863 (s : N.State) (i : N.Inputs) :
  R.v20863 (state s) (inputs i) = Zmod.unsigned (N.v20863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20863 s i)) at 1.
  unfold R.v20863, N.v20863.
  rewrite ?node_20859.
  rewrite ?node_20862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20864 (s : N.State) (i : N.Inputs) :
  R.v20864 (state s) (inputs i) = Zmod.unsigned (N.v20864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20864 s i)) at 1.
  unfold R.v20864, N.v20864.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20865 (s : N.State) (i : N.Inputs) :
  R.v20865 (state s) (inputs i) = Zmod.unsigned (N.v20865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20865 s i)) at 1.
  unfold R.v20865, N.v20865.
  rewrite ?node_7289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20866 (s : N.State) (i : N.Inputs) :
  R.v20866 (state s) (inputs i) = Zmod.unsigned (N.v20866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20866 s i)) at 1.
  unfold R.v20866, N.v20866.
  unfold R.v6, N.v6.
  rewrite !state_r493_nr_5F493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r493_nr_5F493 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20867 (s : N.State) (i : N.Inputs) :
  R.v20867 (state s) (inputs i) = Zmod.unsigned (N.v20867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20867 s i)) at 1.
  unfold R.v20867, N.v20867.
  unfold R.v6, N.v6.
  rewrite ?node_7285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20868 (s : N.State) (i : N.Inputs) :
  R.v20868 (state s) (inputs i) = Zmod.unsigned (N.v20868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20868 s i)) at 1.
  unfold R.v20868, N.v20868.
  rewrite ?node_20866.
  rewrite ?node_20867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20869 (s : N.State) (i : N.Inputs) :
  R.v20869 (state s) (inputs i) = Zmod.unsigned (N.v20869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20869 s i)) at 1.
  unfold R.v20869, N.v20869.
  unfold R.v16484, N.v16484.
  rewrite ?node_20868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20870 (s : N.State) (i : N.Inputs) :
  R.v20870 (state s) (inputs i) = Zmod.unsigned (N.v20870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20870 s i)) at 1.
  unfold R.v20870, N.v20870.
  rewrite ?node_20865.
  rewrite ?node_20869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20871 (s : N.State) (i : N.Inputs) :
  R.v20871 (state s) (inputs i) = Zmod.unsigned (N.v20871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20871 s i)) at 1.
  unfold R.v20871, N.v20871.
  unfold R.v6, N.v6.
  rewrite ?node_20870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20872 (s : N.State) (i : N.Inputs) :
  R.v20872 (state s) (inputs i) = Zmod.unsigned (N.v20872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20872 s i)) at 1.
  unfold R.v20872, N.v20872.
  rewrite ?node_7290.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20873 (s : N.State) (i : N.Inputs) :
  R.v20873 (state s) (inputs i) = Zmod.unsigned (N.v20873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20873 s i)) at 1.
  unfold R.v20873, N.v20873.
  unfold R.v6, N.v6.
  rewrite ?node_7433.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20874 (s : N.State) (i : N.Inputs) :
  R.v20874 (state s) (inputs i) = Zmod.unsigned (N.v20874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20874 s i)) at 1.
  unfold R.v20874, N.v20874.
  rewrite ?node_20872.
  rewrite ?node_20873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20875 (s : N.State) (i : N.Inputs) :
  R.v20875 (state s) (inputs i) = Zmod.unsigned (N.v20875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20875 s i)) at 1.
  unfold R.v20875, N.v20875.
  rewrite ?node_20871.
  rewrite ?node_20874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20876 (s : N.State) (i : N.Inputs) :
  R.v20876 (state s) (inputs i) = Zmod.unsigned (N.v20876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20876 s i)) at 1.
  unfold R.v20876, N.v20876.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20877 (s : N.State) (i : N.Inputs) :
  R.v20877 (state s) (inputs i) = Zmod.unsigned (N.v20877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20877 s i)) at 1.
  unfold R.v20877, N.v20877.
  rewrite ?node_7297.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20878 (s : N.State) (i : N.Inputs) :
  R.v20878 (state s) (inputs i) = Zmod.unsigned (N.v20878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20878 s i)) at 1.
  unfold R.v20878, N.v20878.
  unfold R.v16463, N.v16463.
  rewrite !state_r497_nr_5F497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r497_nr_5F497 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20879 (s : N.State) (i : N.Inputs) :
  R.v20879 (state s) (inputs i) = Zmod.unsigned (N.v20879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20879 s i)) at 1.
  unfold R.v20879, N.v20879.
  unfold R.v16463, N.v16463.
  rewrite !state_r496_nr_5F496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r496_nr_5F496 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20880 (s : N.State) (i : N.Inputs) :
  R.v20880 (state s) (inputs i) = Zmod.unsigned (N.v20880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20880 s i)) at 1.
  unfold R.v20880, N.v20880.
  unfold R.v6, N.v6.
  rewrite !state_r495_nr_5F495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r495_nr_5F495 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20881 (s : N.State) (i : N.Inputs) :
  R.v20881 (state s) (inputs i) = Zmod.unsigned (N.v20881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20881 s i)) at 1.
  unfold R.v20881, N.v20881.
  unfold R.v6, N.v6.
  rewrite !state_r494_nr_5F494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r494_nr_5F494 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20882 (s : N.State) (i : N.Inputs) :
  R.v20882 (state s) (inputs i) = Zmod.unsigned (N.v20882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20882 s i)) at 1.
  unfold R.v20882, N.v20882.
  rewrite ?node_20880.
  rewrite ?node_20881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20883 (s : N.State) (i : N.Inputs) :
  R.v20883 (state s) (inputs i) = Zmod.unsigned (N.v20883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20883 s i)) at 1.
  unfold R.v20883, N.v20883.
  unfold R.v16484, N.v16484.
  rewrite ?node_20882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20884 (s : N.State) (i : N.Inputs) :
  R.v20884 (state s) (inputs i) = Zmod.unsigned (N.v20884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20884 s i)) at 1.
  unfold R.v20884, N.v20884.
  rewrite ?node_20877.
  rewrite ?node_20878.
  rewrite ?node_20879.
  rewrite ?node_20883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20885 (s : N.State) (i : N.Inputs) :
  R.v20885 (state s) (inputs i) = Zmod.unsigned (N.v20885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20885 s i)) at 1.
  unfold R.v20885, N.v20885.
  unfold R.v6, N.v6.
  rewrite ?node_20884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20886 (s : N.State) (i : N.Inputs) :
  R.v20886 (state s) (inputs i) = Zmod.unsigned (N.v20886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20886 s i)) at 1.
  unfold R.v20886, N.v20886.
  rewrite ?node_7298.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20887 (s : N.State) (i : N.Inputs) :
  R.v20887 (state s) (inputs i) = Zmod.unsigned (N.v20887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20887 s i)) at 1.
  unfold R.v20887, N.v20887.
  unfold R.v6, N.v6.
  rewrite ?node_7401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20888 (s : N.State) (i : N.Inputs) :
  R.v20888 (state s) (inputs i) = Zmod.unsigned (N.v20888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20888 s i)) at 1.
  unfold R.v20888, N.v20888.
  unfold R.v6, N.v6.
  rewrite ?node_7436.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20889 (s : N.State) (i : N.Inputs) :
  R.v20889 (state s) (inputs i) = Zmod.unsigned (N.v20889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20889 s i)) at 1.
  unfold R.v20889, N.v20889.
  rewrite ?node_20886.
  rewrite ?node_20887.
  rewrite ?node_20888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20890 (s : N.State) (i : N.Inputs) :
  R.v20890 (state s) (inputs i) = Zmod.unsigned (N.v20890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20890 s i)) at 1.
  unfold R.v20890, N.v20890.
  rewrite ?node_20885.
  rewrite ?node_20889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20891 (s : N.State) (i : N.Inputs) :
  R.v20891 (state s) (inputs i) = Zmod.unsigned (N.v20891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20891 s i)) at 1.
  unfold R.v20891, N.v20891.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20892 (s : N.State) (i : N.Inputs) :
  R.v20892 (state s) (inputs i) = Zmod.unsigned (N.v20892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20892 s i)) at 1.
  unfold R.v20892, N.v20892.
  unfold R.v16463, N.v16463.
  rewrite !state_r496_nr_5F496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r496_nr_5F496 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20893 (s : N.State) (i : N.Inputs) :
  R.v20893 (state s) (inputs i) = Zmod.unsigned (N.v20893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20893 s i)) at 1.
  unfold R.v20893, N.v20893.
  unfold R.v6, N.v6.
  rewrite !state_r495_nr_5F495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r495_nr_5F495 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20894 (s : N.State) (i : N.Inputs) :
  R.v20894 (state s) (inputs i) = Zmod.unsigned (N.v20894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20894 s i)) at 1.
  unfold R.v20894, N.v20894.
  unfold R.v6, N.v6.
  rewrite !state_r494_nr_5F494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r494_nr_5F494 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20895 (s : N.State) (i : N.Inputs) :
  R.v20895 (state s) (inputs i) = Zmod.unsigned (N.v20895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20895 s i)) at 1.
  unfold R.v20895, N.v20895.
  rewrite ?node_20893.
  rewrite ?node_20894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20896 (s : N.State) (i : N.Inputs) :
  R.v20896 (state s) (inputs i) = Zmod.unsigned (N.v20896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20896 s i)) at 1.
  unfold R.v20896, N.v20896.
  unfold R.v16484, N.v16484.
  rewrite ?node_20895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20897 (s : N.State) (i : N.Inputs) :
  R.v20897 (state s) (inputs i) = Zmod.unsigned (N.v20897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20897 s i)) at 1.
  unfold R.v20897, N.v20897.
  rewrite ?node_20892.
  rewrite ?node_20896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20898 (s : N.State) (i : N.Inputs) :
  R.v20898 (state s) (inputs i) = Zmod.unsigned (N.v20898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20898 s i)) at 1.
  unfold R.v20898, N.v20898.
  unfold R.v6, N.v6.
  rewrite ?node_20897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20899 (s : N.State) (i : N.Inputs) :
  R.v20899 (state s) (inputs i) = Zmod.unsigned (N.v20899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20899 s i)) at 1.
  unfold R.v20899, N.v20899.
  rewrite ?node_7293.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20900 (s : N.State) (i : N.Inputs) :
  R.v20900 (state s) (inputs i) = Zmod.unsigned (N.v20900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20900 s i)) at 1.
  unfold R.v20900, N.v20900.
  unfold R.v6, N.v6.
  rewrite ?node_7401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20901 (s : N.State) (i : N.Inputs) :
  R.v20901 (state s) (inputs i) = Zmod.unsigned (N.v20901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20901 s i)) at 1.
  unfold R.v20901, N.v20901.
  rewrite ?node_20899.
  rewrite ?node_20900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20902 (s : N.State) (i : N.Inputs) :
  R.v20902 (state s) (inputs i) = Zmod.unsigned (N.v20902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20902 s i)) at 1.
  unfold R.v20902, N.v20902.
  rewrite ?node_20898.
  rewrite ?node_20901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20903 (s : N.State) (i : N.Inputs) :
  R.v20903 (state s) (inputs i) = Zmod.unsigned (N.v20903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20903 s i)) at 1.
  unfold R.v20903, N.v20903.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20904 (s : N.State) (i : N.Inputs) :
  R.v20904 (state s) (inputs i) = Zmod.unsigned (N.v20904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20904 s i)) at 1.
  unfold R.v20904, N.v20904.
  rewrite ?node_7297.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20905 (s : N.State) (i : N.Inputs) :
  R.v20905 (state s) (inputs i) = Zmod.unsigned (N.v20905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20905 s i)) at 1.
  unfold R.v20905, N.v20905.
  unfold R.v6, N.v6.
  rewrite !state_r497_nr_5F497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r497_nr_5F497 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20906 (s : N.State) (i : N.Inputs) :
  R.v20906 (state s) (inputs i) = Zmod.unsigned (N.v20906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20906 s i)) at 1.
  unfold R.v20906, N.v20906.
  unfold R.v6, N.v6.
  rewrite ?node_7293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20907 (s : N.State) (i : N.Inputs) :
  R.v20907 (state s) (inputs i) = Zmod.unsigned (N.v20907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20907 s i)) at 1.
  unfold R.v20907, N.v20907.
  rewrite ?node_20905.
  rewrite ?node_20906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20908 (s : N.State) (i : N.Inputs) :
  R.v20908 (state s) (inputs i) = Zmod.unsigned (N.v20908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20908 s i)) at 1.
  unfold R.v20908, N.v20908.
  unfold R.v16484, N.v16484.
  rewrite ?node_20907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20909 (s : N.State) (i : N.Inputs) :
  R.v20909 (state s) (inputs i) = Zmod.unsigned (N.v20909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20909 s i)) at 1.
  unfold R.v20909, N.v20909.
  rewrite ?node_20904.
  rewrite ?node_20908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20910 (s : N.State) (i : N.Inputs) :
  R.v20910 (state s) (inputs i) = Zmod.unsigned (N.v20910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20910 s i)) at 1.
  unfold R.v20910, N.v20910.
  unfold R.v6, N.v6.
  rewrite ?node_20909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20911 (s : N.State) (i : N.Inputs) :
  R.v20911 (state s) (inputs i) = Zmod.unsigned (N.v20911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20911 s i)) at 1.
  unfold R.v20911, N.v20911.
  rewrite ?node_7298.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20912 (s : N.State) (i : N.Inputs) :
  R.v20912 (state s) (inputs i) = Zmod.unsigned (N.v20912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20912 s i)) at 1.
  unfold R.v20912, N.v20912.
  unfold R.v6, N.v6.
  rewrite ?node_7436.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20913 (s : N.State) (i : N.Inputs) :
  R.v20913 (state s) (inputs i) = Zmod.unsigned (N.v20913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20913 s i)) at 1.
  unfold R.v20913, N.v20913.
  rewrite ?node_20911.
  rewrite ?node_20912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20914 (s : N.State) (i : N.Inputs) :
  R.v20914 (state s) (inputs i) = Zmod.unsigned (N.v20914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20914 s i)) at 1.
  unfold R.v20914, N.v20914.
  rewrite ?node_20910.
  rewrite ?node_20913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20915 (s : N.State) (i : N.Inputs) :
  R.v20915 (state s) (inputs i) = Zmod.unsigned (N.v20915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20915 s i)) at 1.
  unfold R.v20915, N.v20915.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20916 (s : N.State) (i : N.Inputs) :
  R.v20916 (state s) (inputs i) = Zmod.unsigned (N.v20916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20916 s i)) at 1.
  unfold R.v20916, N.v20916.
  rewrite ?node_7309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20917 (s : N.State) (i : N.Inputs) :
  R.v20917 (state s) (inputs i) = Zmod.unsigned (N.v20917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20917 s i)) at 1.
  unfold R.v20917, N.v20917.
  unfold R.v16463, N.v16463.
  rewrite !state_r501_nr_5F501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r501_nr_5F501 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20918 (s : N.State) (i : N.Inputs) :
  R.v20918 (state s) (inputs i) = Zmod.unsigned (N.v20918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20918 s i)) at 1.
  unfold R.v20918, N.v20918.
  unfold R.v16463, N.v16463.
  rewrite !state_r500_nr_5F500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r500_nr_5F500 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20919 (s : N.State) (i : N.Inputs) :
  R.v20919 (state s) (inputs i) = Zmod.unsigned (N.v20919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20919 s i)) at 1.
  unfold R.v20919, N.v20919.
  unfold R.v6, N.v6.
  rewrite !state_r499_nr_5F499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r499_nr_5F499 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20920 (s : N.State) (i : N.Inputs) :
  R.v20920 (state s) (inputs i) = Zmod.unsigned (N.v20920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20920 s i)) at 1.
  unfold R.v20920, N.v20920.
  unfold R.v6, N.v6.
  rewrite !state_r498_nr_5F498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r498_nr_5F498 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20921 (s : N.State) (i : N.Inputs) :
  R.v20921 (state s) (inputs i) = Zmod.unsigned (N.v20921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20921 s i)) at 1.
  unfold R.v20921, N.v20921.
  rewrite ?node_20919.
  rewrite ?node_20920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20922 (s : N.State) (i : N.Inputs) :
  R.v20922 (state s) (inputs i) = Zmod.unsigned (N.v20922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20922 s i)) at 1.
  unfold R.v20922, N.v20922.
  unfold R.v16484, N.v16484.
  rewrite ?node_20921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20923 (s : N.State) (i : N.Inputs) :
  R.v20923 (state s) (inputs i) = Zmod.unsigned (N.v20923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20923 s i)) at 1.
  unfold R.v20923, N.v20923.
  rewrite ?node_20916.
  rewrite ?node_20917.
  rewrite ?node_20918.
  rewrite ?node_20922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20924 (s : N.State) (i : N.Inputs) :
  R.v20924 (state s) (inputs i) = Zmod.unsigned (N.v20924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20924 s i)) at 1.
  unfold R.v20924, N.v20924.
  unfold R.v6, N.v6.
  rewrite ?node_20923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20925 (s : N.State) (i : N.Inputs) :
  R.v20925 (state s) (inputs i) = Zmod.unsigned (N.v20925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20925 s i)) at 1.
  unfold R.v20925, N.v20925.
  rewrite ?node_7310.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20926 (s : N.State) (i : N.Inputs) :
  R.v20926 (state s) (inputs i) = Zmod.unsigned (N.v20926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20926 s i)) at 1.
  unfold R.v20926, N.v20926.
  unfold R.v6, N.v6.
  rewrite ?node_7413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20927 (s : N.State) (i : N.Inputs) :
  R.v20927 (state s) (inputs i) = Zmod.unsigned (N.v20927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20927 s i)) at 1.
  unfold R.v20927, N.v20927.
  unfold R.v6, N.v6.
  rewrite ?node_7440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20928 (s : N.State) (i : N.Inputs) :
  R.v20928 (state s) (inputs i) = Zmod.unsigned (N.v20928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20928 s i)) at 1.
  unfold R.v20928, N.v20928.
  rewrite ?node_20925.
  rewrite ?node_20926.
  rewrite ?node_20927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20929 (s : N.State) (i : N.Inputs) :
  R.v20929 (state s) (inputs i) = Zmod.unsigned (N.v20929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20929 s i)) at 1.
  unfold R.v20929, N.v20929.
  rewrite ?node_20924.
  rewrite ?node_20928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20930 (s : N.State) (i : N.Inputs) :
  R.v20930 (state s) (inputs i) = Zmod.unsigned (N.v20930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20930 s i)) at 1.
  unfold R.v20930, N.v20930.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20931 (s : N.State) (i : N.Inputs) :
  R.v20931 (state s) (inputs i) = Zmod.unsigned (N.v20931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20931 s i)) at 1.
  unfold R.v20931, N.v20931.
  unfold R.v16463, N.v16463.
  rewrite !state_r500_nr_5F500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r500_nr_5F500 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20932 (s : N.State) (i : N.Inputs) :
  R.v20932 (state s) (inputs i) = Zmod.unsigned (N.v20932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20932 s i)) at 1.
  unfold R.v20932, N.v20932.
  unfold R.v6, N.v6.
  rewrite !state_r499_nr_5F499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r499_nr_5F499 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20933 (s : N.State) (i : N.Inputs) :
  R.v20933 (state s) (inputs i) = Zmod.unsigned (N.v20933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20933 s i)) at 1.
  unfold R.v20933, N.v20933.
  unfold R.v6, N.v6.
  rewrite !state_r498_nr_5F498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r498_nr_5F498 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20934 (s : N.State) (i : N.Inputs) :
  R.v20934 (state s) (inputs i) = Zmod.unsigned (N.v20934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20934 s i)) at 1.
  unfold R.v20934, N.v20934.
  rewrite ?node_20932.
  rewrite ?node_20933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20935 (s : N.State) (i : N.Inputs) :
  R.v20935 (state s) (inputs i) = Zmod.unsigned (N.v20935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20935 s i)) at 1.
  unfold R.v20935, N.v20935.
  unfold R.v16484, N.v16484.
  rewrite ?node_20934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20936 (s : N.State) (i : N.Inputs) :
  R.v20936 (state s) (inputs i) = Zmod.unsigned (N.v20936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20936 s i)) at 1.
  unfold R.v20936, N.v20936.
  rewrite ?node_20931.
  rewrite ?node_20935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20937 (s : N.State) (i : N.Inputs) :
  R.v20937 (state s) (inputs i) = Zmod.unsigned (N.v20937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20937 s i)) at 1.
  unfold R.v20937, N.v20937.
  unfold R.v6, N.v6.
  rewrite ?node_20936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20938 (s : N.State) (i : N.Inputs) :
  R.v20938 (state s) (inputs i) = Zmod.unsigned (N.v20938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20938 s i)) at 1.
  unfold R.v20938, N.v20938.
  rewrite ?node_7305.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20939 (s : N.State) (i : N.Inputs) :
  R.v20939 (state s) (inputs i) = Zmod.unsigned (N.v20939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20939 s i)) at 1.
  unfold R.v20939, N.v20939.
  unfold R.v6, N.v6.
  rewrite ?node_7413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20940 (s : N.State) (i : N.Inputs) :
  R.v20940 (state s) (inputs i) = Zmod.unsigned (N.v20940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20940 s i)) at 1.
  unfold R.v20940, N.v20940.
  rewrite ?node_20938.
  rewrite ?node_20939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20941 (s : N.State) (i : N.Inputs) :
  R.v20941 (state s) (inputs i) = Zmod.unsigned (N.v20941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20941 s i)) at 1.
  unfold R.v20941, N.v20941.
  rewrite ?node_20937.
  rewrite ?node_20940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20942 (s : N.State) (i : N.Inputs) :
  R.v20942 (state s) (inputs i) = Zmod.unsigned (N.v20942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20942 s i)) at 1.
  unfold R.v20942, N.v20942.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20943 (s : N.State) (i : N.Inputs) :
  R.v20943 (state s) (inputs i) = Zmod.unsigned (N.v20943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20943 s i)) at 1.
  unfold R.v20943, N.v20943.
  rewrite ?node_7309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20944 (s : N.State) (i : N.Inputs) :
  R.v20944 (state s) (inputs i) = Zmod.unsigned (N.v20944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20944 s i)) at 1.
  unfold R.v20944, N.v20944.
  unfold R.v6, N.v6.
  rewrite !state_r501_nr_5F501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r501_nr_5F501 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20945 (s : N.State) (i : N.Inputs) :
  R.v20945 (state s) (inputs i) = Zmod.unsigned (N.v20945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20945 s i)) at 1.
  unfold R.v20945, N.v20945.
  unfold R.v6, N.v6.
  rewrite ?node_7305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20946 (s : N.State) (i : N.Inputs) :
  R.v20946 (state s) (inputs i) = Zmod.unsigned (N.v20946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20946 s i)) at 1.
  unfold R.v20946, N.v20946.
  rewrite ?node_20944.
  rewrite ?node_20945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20947 (s : N.State) (i : N.Inputs) :
  R.v20947 (state s) (inputs i) = Zmod.unsigned (N.v20947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20947 s i)) at 1.
  unfold R.v20947, N.v20947.
  unfold R.v16484, N.v16484.
  rewrite ?node_20946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20948 (s : N.State) (i : N.Inputs) :
  R.v20948 (state s) (inputs i) = Zmod.unsigned (N.v20948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20948 s i)) at 1.
  unfold R.v20948, N.v20948.
  rewrite ?node_20943.
  rewrite ?node_20947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20949 (s : N.State) (i : N.Inputs) :
  R.v20949 (state s) (inputs i) = Zmod.unsigned (N.v20949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20949 s i)) at 1.
  unfold R.v20949, N.v20949.
  unfold R.v6, N.v6.
  rewrite ?node_20948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20950 (s : N.State) (i : N.Inputs) :
  R.v20950 (state s) (inputs i) = Zmod.unsigned (N.v20950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20950 s i)) at 1.
  unfold R.v20950, N.v20950.
  rewrite ?node_7310.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20951 (s : N.State) (i : N.Inputs) :
  R.v20951 (state s) (inputs i) = Zmod.unsigned (N.v20951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20951 s i)) at 1.
  unfold R.v20951, N.v20951.
  unfold R.v6, N.v6.
  rewrite ?node_7440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20952 (s : N.State) (i : N.Inputs) :
  R.v20952 (state s) (inputs i) = Zmod.unsigned (N.v20952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20952 s i)) at 1.
  unfold R.v20952, N.v20952.
  rewrite ?node_20950.
  rewrite ?node_20951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20953 (s : N.State) (i : N.Inputs) :
  R.v20953 (state s) (inputs i) = Zmod.unsigned (N.v20953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20953 s i)) at 1.
  unfold R.v20953, N.v20953.
  rewrite ?node_20949.
  rewrite ?node_20952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20954 (s : N.State) (i : N.Inputs) :
  R.v20954 (state s) (inputs i) = Zmod.unsigned (N.v20954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20954 s i)) at 1.
  unfold R.v20954, N.v20954.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20955 (s : N.State) (i : N.Inputs) :
  R.v20955 (state s) (inputs i) = Zmod.unsigned (N.v20955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20955 s i)) at 1.
  unfold R.v20955, N.v20955.
  unfold R.v6, N.v6.
  rewrite !state_r503_nr_5F503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r503_nr_5F503 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20956 (s : N.State) (i : N.Inputs) :
  R.v20956 (state s) (inputs i) = Zmod.unsigned (N.v20956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20956 s i)) at 1.
  unfold R.v20956, N.v20956.
  unfold R.v6, N.v6.
  rewrite !state_r502_nr_5F502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r502_nr_5F502 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20957 (s : N.State) (i : N.Inputs) :
  R.v20957 (state s) (inputs i) = Zmod.unsigned (N.v20957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20957 s i)) at 1.
  unfold R.v20957, N.v20957.
  rewrite ?node_20955.
  rewrite ?node_20956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20958 (s : N.State) (i : N.Inputs) :
  R.v20958 (state s) (inputs i) = Zmod.unsigned (N.v20958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20958 s i)) at 1.
  unfold R.v20958, N.v20958.
  unfold R.v16463, N.v16463.
  rewrite ?node_20957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20959 (s : N.State) (i : N.Inputs) :
  R.v20959 (state s) (inputs i) = Zmod.unsigned (N.v20959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20959 s i)) at 1.
  unfold R.v20959, N.v20959.
  rewrite ?node_7311.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20960 (s : N.State) (i : N.Inputs) :
  R.v20960 (state s) (inputs i) = Zmod.unsigned (N.v20960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20960 s i)) at 1.
  unfold R.v20960, N.v20960.
  unfold R.v6, N.v6.
  rewrite ?node_7442.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20961 (s : N.State) (i : N.Inputs) :
  R.v20961 (state s) (inputs i) = Zmod.unsigned (N.v20961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20961 s i)) at 1.
  unfold R.v20961, N.v20961.
  rewrite ?node_20959.
  rewrite ?node_20960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20962 (s : N.State) (i : N.Inputs) :
  R.v20962 (state s) (inputs i) = Zmod.unsigned (N.v20962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20962 s i)) at 1.
  unfold R.v20962, N.v20962.
  rewrite ?node_20958.
  rewrite ?node_20961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20963 (s : N.State) (i : N.Inputs) :
  R.v20963 (state s) (inputs i) = Zmod.unsigned (N.v20963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20963 s i)) at 1.
  unfold R.v20963, N.v20963.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20964 (s : N.State) (i : N.Inputs) :
  R.v20964 (state s) (inputs i) = Zmod.unsigned (N.v20964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20964 s i)) at 1.
  unfold R.v20964, N.v20964.
  rewrite ?node_7378.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20965 (s : N.State) (i : N.Inputs) :
  R.v20965 (state s) (inputs i) = Zmod.unsigned (N.v20965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20965 s i)) at 1.
  unfold R.v20965, N.v20965.
  unfold R.v16463, N.v16463.
  rewrite !state_r507_nr_5F507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r507_nr_5F507 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20966 (s : N.State) (i : N.Inputs) :
  R.v20966 (state s) (inputs i) = Zmod.unsigned (N.v20966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20966 s i)) at 1.
  unfold R.v20966, N.v20966.
  unfold R.v16463, N.v16463.
  rewrite !state_r506_nr_5F506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r506_nr_5F506 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20967 (s : N.State) (i : N.Inputs) :
  R.v20967 (state s) (inputs i) = Zmod.unsigned (N.v20967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20967 s i)) at 1.
  unfold R.v20967, N.v20967.
  unfold R.v6, N.v6.
  rewrite !state_r505_nr_5F505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r505_nr_5F505 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20968 (s : N.State) (i : N.Inputs) :
  R.v20968 (state s) (inputs i) = Zmod.unsigned (N.v20968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20968 s i)) at 1.
  unfold R.v20968, N.v20968.
  unfold R.v6, N.v6.
  rewrite !state_r504_nr_5F504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r504_nr_5F504 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20969 (s : N.State) (i : N.Inputs) :
  R.v20969 (state s) (inputs i) = Zmod.unsigned (N.v20969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20969 s i)) at 1.
  unfold R.v20969, N.v20969.
  rewrite ?node_20967.
  rewrite ?node_20968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20970 (s : N.State) (i : N.Inputs) :
  R.v20970 (state s) (inputs i) = Zmod.unsigned (N.v20970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20970 s i)) at 1.
  unfold R.v20970, N.v20970.
  unfold R.v16484, N.v16484.
  rewrite ?node_20969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20971 (s : N.State) (i : N.Inputs) :
  R.v20971 (state s) (inputs i) = Zmod.unsigned (N.v20971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20971 s i)) at 1.
  unfold R.v20971, N.v20971.
  rewrite ?node_20964.
  rewrite ?node_20965.
  rewrite ?node_20966.
  rewrite ?node_20970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20972 (s : N.State) (i : N.Inputs) :
  R.v20972 (state s) (inputs i) = Zmod.unsigned (N.v20972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20972 s i)) at 1.
  unfold R.v20972, N.v20972.
  unfold R.v6, N.v6.
  rewrite ?node_20971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20973 (s : N.State) (i : N.Inputs) :
  R.v20973 (state s) (inputs i) = Zmod.unsigned (N.v20973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20973 s i)) at 1.
  unfold R.v20973, N.v20973.
  rewrite ?node_7379.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20974 (s : N.State) (i : N.Inputs) :
  R.v20974 (state s) (inputs i) = Zmod.unsigned (N.v20974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20974 s i)) at 1.
  unfold R.v20974, N.v20974.
  unfold R.v6, N.v6.
  rewrite ?node_7485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20975 (s : N.State) (i : N.Inputs) :
  R.v20975 (state s) (inputs i) = Zmod.unsigned (N.v20975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20975 s i)) at 1.
  unfold R.v20975, N.v20975.
  unfold R.v6, N.v6.
  rewrite ?node_7527.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20976 (s : N.State) (i : N.Inputs) :
  R.v20976 (state s) (inputs i) = Zmod.unsigned (N.v20976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20976 s i)) at 1.
  unfold R.v20976, N.v20976.
  rewrite ?node_20973.
  rewrite ?node_20974.
  rewrite ?node_20975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20977 (s : N.State) (i : N.Inputs) :
  R.v20977 (state s) (inputs i) = Zmod.unsigned (N.v20977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20977 s i)) at 1.
  unfold R.v20977, N.v20977.
  rewrite ?node_20972.
  rewrite ?node_20976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20978 (s : N.State) (i : N.Inputs) :
  R.v20978 (state s) (inputs i) = Zmod.unsigned (N.v20978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20978 s i)) at 1.
  unfold R.v20978, N.v20978.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20979 (s : N.State) (i : N.Inputs) :
  R.v20979 (state s) (inputs i) = Zmod.unsigned (N.v20979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20979 s i)) at 1.
  unfold R.v20979, N.v20979.
  unfold R.v16463, N.v16463.
  rewrite !state_r506_nr_5F506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r506_nr_5F506 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20980 (s : N.State) (i : N.Inputs) :
  R.v20980 (state s) (inputs i) = Zmod.unsigned (N.v20980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20980 s i)) at 1.
  unfold R.v20980, N.v20980.
  unfold R.v6, N.v6.
  rewrite !state_r505_nr_5F505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r505_nr_5F505 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20981 (s : N.State) (i : N.Inputs) :
  R.v20981 (state s) (inputs i) = Zmod.unsigned (N.v20981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20981 s i)) at 1.
  unfold R.v20981, N.v20981.
  unfold R.v6, N.v6.
  rewrite !state_r504_nr_5F504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r504_nr_5F504 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20982 (s : N.State) (i : N.Inputs) :
  R.v20982 (state s) (inputs i) = Zmod.unsigned (N.v20982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20982 s i)) at 1.
  unfold R.v20982, N.v20982.
  rewrite ?node_20980.
  rewrite ?node_20981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20983 (s : N.State) (i : N.Inputs) :
  R.v20983 (state s) (inputs i) = Zmod.unsigned (N.v20983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20983 s i)) at 1.
  unfold R.v20983, N.v20983.
  unfold R.v16484, N.v16484.
  rewrite ?node_20982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20984 (s : N.State) (i : N.Inputs) :
  R.v20984 (state s) (inputs i) = Zmod.unsigned (N.v20984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20984 s i)) at 1.
  unfold R.v20984, N.v20984.
  rewrite ?node_20979.
  rewrite ?node_20983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20985 (s : N.State) (i : N.Inputs) :
  R.v20985 (state s) (inputs i) = Zmod.unsigned (N.v20985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20985 s i)) at 1.
  unfold R.v20985, N.v20985.
  unfold R.v6, N.v6.
  rewrite ?node_20984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20986 (s : N.State) (i : N.Inputs) :
  R.v20986 (state s) (inputs i) = Zmod.unsigned (N.v20986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20986 s i)) at 1.
  unfold R.v20986, N.v20986.
  rewrite ?node_7374.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20987 (s : N.State) (i : N.Inputs) :
  R.v20987 (state s) (inputs i) = Zmod.unsigned (N.v20987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20987 s i)) at 1.
  unfold R.v20987, N.v20987.
  unfold R.v6, N.v6.
  rewrite ?node_7485.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20988 (s : N.State) (i : N.Inputs) :
  R.v20988 (state s) (inputs i) = Zmod.unsigned (N.v20988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20988 s i)) at 1.
  unfold R.v20988, N.v20988.
  rewrite ?node_20986.
  rewrite ?node_20987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20989 (s : N.State) (i : N.Inputs) :
  R.v20989 (state s) (inputs i) = Zmod.unsigned (N.v20989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20989 s i)) at 1.
  unfold R.v20989, N.v20989.
  rewrite ?node_20985.
  rewrite ?node_20988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20990 (s : N.State) (i : N.Inputs) :
  R.v20990 (state s) (inputs i) = Zmod.unsigned (N.v20990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20990 s i)) at 1.
  unfold R.v20990, N.v20990.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20991 (s : N.State) (i : N.Inputs) :
  R.v20991 (state s) (inputs i) = Zmod.unsigned (N.v20991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20991 s i)) at 1.
  unfold R.v20991, N.v20991.
  rewrite ?node_7378.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20992 (s : N.State) (i : N.Inputs) :
  R.v20992 (state s) (inputs i) = Zmod.unsigned (N.v20992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20992 s i)) at 1.
  unfold R.v20992, N.v20992.
  unfold R.v6, N.v6.
  rewrite !state_r507_nr_5F507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r507_nr_5F507 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20993 (s : N.State) (i : N.Inputs) :
  R.v20993 (state s) (inputs i) = Zmod.unsigned (N.v20993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20993 s i)) at 1.
  unfold R.v20993, N.v20993.
  unfold R.v6, N.v6.
  rewrite ?node_7374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20994 (s : N.State) (i : N.Inputs) :
  R.v20994 (state s) (inputs i) = Zmod.unsigned (N.v20994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20994 s i)) at 1.
  unfold R.v20994, N.v20994.
  rewrite ?node_20992.
  rewrite ?node_20993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20995 (s : N.State) (i : N.Inputs) :
  R.v20995 (state s) (inputs i) = Zmod.unsigned (N.v20995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20995 s i)) at 1.
  unfold R.v20995, N.v20995.
  unfold R.v16484, N.v16484.
  rewrite ?node_20994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20996 (s : N.State) (i : N.Inputs) :
  R.v20996 (state s) (inputs i) = Zmod.unsigned (N.v20996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20996 s i)) at 1.
  unfold R.v20996, N.v20996.
  rewrite ?node_20991.
  rewrite ?node_20995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20997 (s : N.State) (i : N.Inputs) :
  R.v20997 (state s) (inputs i) = Zmod.unsigned (N.v20997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20997 s i)) at 1.
  unfold R.v20997, N.v20997.
  unfold R.v6, N.v6.
  rewrite ?node_20996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20998 (s : N.State) (i : N.Inputs) :
  R.v20998 (state s) (inputs i) = Zmod.unsigned (N.v20998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20998 s i)) at 1.
  unfold R.v20998, N.v20998.
  rewrite ?node_7379.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20999 (s : N.State) (i : N.Inputs) :
  R.v20999 (state s) (inputs i) = Zmod.unsigned (N.v20999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20999 s i)) at 1.
  unfold R.v20999, N.v20999.
  unfold R.v6, N.v6.
  rewrite ?node_7527.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
