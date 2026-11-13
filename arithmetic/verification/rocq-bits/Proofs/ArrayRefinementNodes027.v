(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes026.
Lemma node_27000 (s : N.State) (i : N.Inputs) :
  R.v27000 (state s) (inputs i) = Zmod.unsigned (N.v27000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27000 s i)) at 1.
  unfold R.v27000, N.v27000.
  rewrite ?node_26997.
  rewrite ?node_26998.
  rewrite ?node_26999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27001 (s : N.State) (i : N.Inputs) :
  R.v27001 (state s) (inputs i) = Zmod.unsigned (N.v27001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27001 s i)) at 1.
  unfold R.v27001, N.v27001.
  rewrite ?node_26996.
  rewrite ?node_27000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27002 (s : N.State) (i : N.Inputs) :
  R.v27002 (state s) (inputs i) = Zmod.unsigned (N.v27002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27002 s i)) at 1.
  unfold R.v27002, N.v27002.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27003 (s : N.State) (i : N.Inputs) :
  R.v27003 (state s) (inputs i) = Zmod.unsigned (N.v27003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27003 s i)) at 1.
  unfold R.v27003, N.v27003.
  unfold R.v16463, N.v16463.
  rewrite !state_r1146_nr_5F1146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1146_nr_5F1146 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27004 (s : N.State) (i : N.Inputs) :
  R.v27004 (state s) (inputs i) = Zmod.unsigned (N.v27004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27004 s i)) at 1.
  unfold R.v27004, N.v27004.
  unfold R.v6, N.v6.
  rewrite !state_r1145_nr_5F1145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1145_nr_5F1145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27005 (s : N.State) (i : N.Inputs) :
  R.v27005 (state s) (inputs i) = Zmod.unsigned (N.v27005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27005 s i)) at 1.
  unfold R.v27005, N.v27005.
  unfold R.v6, N.v6.
  rewrite !state_r1144_nr_5F1144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1144_nr_5F1144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27006 (s : N.State) (i : N.Inputs) :
  R.v27006 (state s) (inputs i) = Zmod.unsigned (N.v27006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27006 s i)) at 1.
  unfold R.v27006, N.v27006.
  rewrite ?node_27004.
  rewrite ?node_27005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27007 (s : N.State) (i : N.Inputs) :
  R.v27007 (state s) (inputs i) = Zmod.unsigned (N.v27007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27007 s i)) at 1.
  unfold R.v27007, N.v27007.
  unfold R.v16484, N.v16484.
  rewrite ?node_27006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27008 (s : N.State) (i : N.Inputs) :
  R.v27008 (state s) (inputs i) = Zmod.unsigned (N.v27008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27008 s i)) at 1.
  unfold R.v27008, N.v27008.
  rewrite ?node_27003.
  rewrite ?node_27007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27009 (s : N.State) (i : N.Inputs) :
  R.v27009 (state s) (inputs i) = Zmod.unsigned (N.v27009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27009 s i)) at 1.
  unfold R.v27009, N.v27009.
  unfold R.v6, N.v6.
  rewrite ?node_27008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27010 (s : N.State) (i : N.Inputs) :
  R.v27010 (state s) (inputs i) = Zmod.unsigned (N.v27010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27010 s i)) at 1.
  unfold R.v27010, N.v27010.
  rewrite ?node_10332.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27011 (s : N.State) (i : N.Inputs) :
  R.v27011 (state s) (inputs i) = Zmod.unsigned (N.v27011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27011 s i)) at 1.
  unfold R.v27011, N.v27011.
  unfold R.v6, N.v6.
  rewrite ?node_10494.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27012 (s : N.State) (i : N.Inputs) :
  R.v27012 (state s) (inputs i) = Zmod.unsigned (N.v27012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27012 s i)) at 1.
  unfold R.v27012, N.v27012.
  rewrite ?node_27010.
  rewrite ?node_27011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27013 (s : N.State) (i : N.Inputs) :
  R.v27013 (state s) (inputs i) = Zmod.unsigned (N.v27013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27013 s i)) at 1.
  unfold R.v27013, N.v27013.
  rewrite ?node_27009.
  rewrite ?node_27012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27014 (s : N.State) (i : N.Inputs) :
  R.v27014 (state s) (inputs i) = Zmod.unsigned (N.v27014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27014 s i)) at 1.
  unfold R.v27014, N.v27014.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27015 (s : N.State) (i : N.Inputs) :
  R.v27015 (state s) (inputs i) = Zmod.unsigned (N.v27015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27015 s i)) at 1.
  unfold R.v27015, N.v27015.
  rewrite ?node_10336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27016 (s : N.State) (i : N.Inputs) :
  R.v27016 (state s) (inputs i) = Zmod.unsigned (N.v27016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27016 s i)) at 1.
  unfold R.v27016, N.v27016.
  unfold R.v6, N.v6.
  rewrite !state_r1147_nr_5F1147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1147_nr_5F1147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27017 (s : N.State) (i : N.Inputs) :
  R.v27017 (state s) (inputs i) = Zmod.unsigned (N.v27017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27017 s i)) at 1.
  unfold R.v27017, N.v27017.
  unfold R.v6, N.v6.
  rewrite ?node_10332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27018 (s : N.State) (i : N.Inputs) :
  R.v27018 (state s) (inputs i) = Zmod.unsigned (N.v27018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27018 s i)) at 1.
  unfold R.v27018, N.v27018.
  rewrite ?node_27016.
  rewrite ?node_27017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27019 (s : N.State) (i : N.Inputs) :
  R.v27019 (state s) (inputs i) = Zmod.unsigned (N.v27019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27019 s i)) at 1.
  unfold R.v27019, N.v27019.
  unfold R.v16484, N.v16484.
  rewrite ?node_27018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27020 (s : N.State) (i : N.Inputs) :
  R.v27020 (state s) (inputs i) = Zmod.unsigned (N.v27020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27020 s i)) at 1.
  unfold R.v27020, N.v27020.
  rewrite ?node_27015.
  rewrite ?node_27019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27021 (s : N.State) (i : N.Inputs) :
  R.v27021 (state s) (inputs i) = Zmod.unsigned (N.v27021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27021 s i)) at 1.
  unfold R.v27021, N.v27021.
  unfold R.v6, N.v6.
  rewrite ?node_27020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27022 (s : N.State) (i : N.Inputs) :
  R.v27022 (state s) (inputs i) = Zmod.unsigned (N.v27022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27022 s i)) at 1.
  unfold R.v27022, N.v27022.
  rewrite ?node_10337.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27023 (s : N.State) (i : N.Inputs) :
  R.v27023 (state s) (inputs i) = Zmod.unsigned (N.v27023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27023 s i)) at 1.
  unfold R.v27023, N.v27023.
  unfold R.v6, N.v6.
  rewrite ?node_10541.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27024 (s : N.State) (i : N.Inputs) :
  R.v27024 (state s) (inputs i) = Zmod.unsigned (N.v27024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27024 s i)) at 1.
  unfold R.v27024, N.v27024.
  rewrite ?node_27022.
  rewrite ?node_27023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27025 (s : N.State) (i : N.Inputs) :
  R.v27025 (state s) (inputs i) = Zmod.unsigned (N.v27025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27025 s i)) at 1.
  unfold R.v27025, N.v27025.
  rewrite ?node_27021.
  rewrite ?node_27024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27026 (s : N.State) (i : N.Inputs) :
  R.v27026 (state s) (inputs i) = Zmod.unsigned (N.v27026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27026 s i)) at 1.
  unfold R.v27026, N.v27026.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27027 (s : N.State) (i : N.Inputs) :
  R.v27027 (state s) (inputs i) = Zmod.unsigned (N.v27027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27027 s i)) at 1.
  unfold R.v27027, N.v27027.
  rewrite ?node_10344.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27028 (s : N.State) (i : N.Inputs) :
  R.v27028 (state s) (inputs i) = Zmod.unsigned (N.v27028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27028 s i)) at 1.
  unfold R.v27028, N.v27028.
  unfold R.v16463, N.v16463.
  rewrite !state_r1151_nr_5F1151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1151_nr_5F1151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27029 (s : N.State) (i : N.Inputs) :
  R.v27029 (state s) (inputs i) = Zmod.unsigned (N.v27029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27029 s i)) at 1.
  unfold R.v27029, N.v27029.
  unfold R.v16463, N.v16463.
  rewrite !state_r1150_nr_5F1150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1150_nr_5F1150 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27030 (s : N.State) (i : N.Inputs) :
  R.v27030 (state s) (inputs i) = Zmod.unsigned (N.v27030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27030 s i)) at 1.
  unfold R.v27030, N.v27030.
  unfold R.v6, N.v6.
  rewrite !state_r1149_nr_5F1149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1149_nr_5F1149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27031 (s : N.State) (i : N.Inputs) :
  R.v27031 (state s) (inputs i) = Zmod.unsigned (N.v27031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27031 s i)) at 1.
  unfold R.v27031, N.v27031.
  unfold R.v6, N.v6.
  rewrite !state_r1148_nr_5F1148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1148_nr_5F1148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27032 (s : N.State) (i : N.Inputs) :
  R.v27032 (state s) (inputs i) = Zmod.unsigned (N.v27032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27032 s i)) at 1.
  unfold R.v27032, N.v27032.
  rewrite ?node_27030.
  rewrite ?node_27031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27033 (s : N.State) (i : N.Inputs) :
  R.v27033 (state s) (inputs i) = Zmod.unsigned (N.v27033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27033 s i)) at 1.
  unfold R.v27033, N.v27033.
  unfold R.v16484, N.v16484.
  rewrite ?node_27032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27034 (s : N.State) (i : N.Inputs) :
  R.v27034 (state s) (inputs i) = Zmod.unsigned (N.v27034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27034 s i)) at 1.
  unfold R.v27034, N.v27034.
  rewrite ?node_27027.
  rewrite ?node_27028.
  rewrite ?node_27029.
  rewrite ?node_27033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27035 (s : N.State) (i : N.Inputs) :
  R.v27035 (state s) (inputs i) = Zmod.unsigned (N.v27035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27035 s i)) at 1.
  unfold R.v27035, N.v27035.
  unfold R.v6, N.v6.
  rewrite ?node_27034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27036 (s : N.State) (i : N.Inputs) :
  R.v27036 (state s) (inputs i) = Zmod.unsigned (N.v27036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27036 s i)) at 1.
  unfold R.v27036, N.v27036.
  rewrite ?node_10345.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27037 (s : N.State) (i : N.Inputs) :
  R.v27037 (state s) (inputs i) = Zmod.unsigned (N.v27037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27037 s i)) at 1.
  unfold R.v27037, N.v27037.
  unfold R.v6, N.v6.
  rewrite ?node_10502.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27038 (s : N.State) (i : N.Inputs) :
  R.v27038 (state s) (inputs i) = Zmod.unsigned (N.v27038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27038 s i)) at 1.
  unfold R.v27038, N.v27038.
  unfold R.v6, N.v6.
  rewrite ?node_10554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27039 (s : N.State) (i : N.Inputs) :
  R.v27039 (state s) (inputs i) = Zmod.unsigned (N.v27039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27039 s i)) at 1.
  unfold R.v27039, N.v27039.
  rewrite ?node_27036.
  rewrite ?node_27037.
  rewrite ?node_27038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27040 (s : N.State) (i : N.Inputs) :
  R.v27040 (state s) (inputs i) = Zmod.unsigned (N.v27040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27040 s i)) at 1.
  unfold R.v27040, N.v27040.
  rewrite ?node_27035.
  rewrite ?node_27039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27041 (s : N.State) (i : N.Inputs) :
  R.v27041 (state s) (inputs i) = Zmod.unsigned (N.v27041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27041 s i)) at 1.
  unfold R.v27041, N.v27041.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27042 (s : N.State) (i : N.Inputs) :
  R.v27042 (state s) (inputs i) = Zmod.unsigned (N.v27042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27042 s i)) at 1.
  unfold R.v27042, N.v27042.
  unfold R.v16463, N.v16463.
  rewrite !state_r1150_nr_5F1150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1150_nr_5F1150 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27043 (s : N.State) (i : N.Inputs) :
  R.v27043 (state s) (inputs i) = Zmod.unsigned (N.v27043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27043 s i)) at 1.
  unfold R.v27043, N.v27043.
  unfold R.v6, N.v6.
  rewrite !state_r1149_nr_5F1149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1149_nr_5F1149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27044 (s : N.State) (i : N.Inputs) :
  R.v27044 (state s) (inputs i) = Zmod.unsigned (N.v27044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27044 s i)) at 1.
  unfold R.v27044, N.v27044.
  unfold R.v6, N.v6.
  rewrite !state_r1148_nr_5F1148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1148_nr_5F1148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27045 (s : N.State) (i : N.Inputs) :
  R.v27045 (state s) (inputs i) = Zmod.unsigned (N.v27045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27045 s i)) at 1.
  unfold R.v27045, N.v27045.
  rewrite ?node_27043.
  rewrite ?node_27044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27046 (s : N.State) (i : N.Inputs) :
  R.v27046 (state s) (inputs i) = Zmod.unsigned (N.v27046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27046 s i)) at 1.
  unfold R.v27046, N.v27046.
  unfold R.v16484, N.v16484.
  rewrite ?node_27045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27047 (s : N.State) (i : N.Inputs) :
  R.v27047 (state s) (inputs i) = Zmod.unsigned (N.v27047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27047 s i)) at 1.
  unfold R.v27047, N.v27047.
  rewrite ?node_27042.
  rewrite ?node_27046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27048 (s : N.State) (i : N.Inputs) :
  R.v27048 (state s) (inputs i) = Zmod.unsigned (N.v27048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27048 s i)) at 1.
  unfold R.v27048, N.v27048.
  unfold R.v6, N.v6.
  rewrite ?node_27047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27049 (s : N.State) (i : N.Inputs) :
  R.v27049 (state s) (inputs i) = Zmod.unsigned (N.v27049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27049 s i)) at 1.
  unfold R.v27049, N.v27049.
  rewrite ?node_10340.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27050 (s : N.State) (i : N.Inputs) :
  R.v27050 (state s) (inputs i) = Zmod.unsigned (N.v27050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27050 s i)) at 1.
  unfold R.v27050, N.v27050.
  unfold R.v6, N.v6.
  rewrite ?node_10502.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27051 (s : N.State) (i : N.Inputs) :
  R.v27051 (state s) (inputs i) = Zmod.unsigned (N.v27051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27051 s i)) at 1.
  unfold R.v27051, N.v27051.
  rewrite ?node_27049.
  rewrite ?node_27050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27052 (s : N.State) (i : N.Inputs) :
  R.v27052 (state s) (inputs i) = Zmod.unsigned (N.v27052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27052 s i)) at 1.
  unfold R.v27052, N.v27052.
  rewrite ?node_27048.
  rewrite ?node_27051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27053 (s : N.State) (i : N.Inputs) :
  R.v27053 (state s) (inputs i) = Zmod.unsigned (N.v27053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27053 s i)) at 1.
  unfold R.v27053, N.v27053.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27054 (s : N.State) (i : N.Inputs) :
  R.v27054 (state s) (inputs i) = Zmod.unsigned (N.v27054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27054 s i)) at 1.
  unfold R.v27054, N.v27054.
  rewrite ?node_10344.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27055 (s : N.State) (i : N.Inputs) :
  R.v27055 (state s) (inputs i) = Zmod.unsigned (N.v27055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27055 s i)) at 1.
  unfold R.v27055, N.v27055.
  unfold R.v6, N.v6.
  rewrite !state_r1151_nr_5F1151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1151_nr_5F1151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27056 (s : N.State) (i : N.Inputs) :
  R.v27056 (state s) (inputs i) = Zmod.unsigned (N.v27056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27056 s i)) at 1.
  unfold R.v27056, N.v27056.
  unfold R.v6, N.v6.
  rewrite ?node_10340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27057 (s : N.State) (i : N.Inputs) :
  R.v27057 (state s) (inputs i) = Zmod.unsigned (N.v27057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27057 s i)) at 1.
  unfold R.v27057, N.v27057.
  rewrite ?node_27055.
  rewrite ?node_27056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27058 (s : N.State) (i : N.Inputs) :
  R.v27058 (state s) (inputs i) = Zmod.unsigned (N.v27058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27058 s i)) at 1.
  unfold R.v27058, N.v27058.
  unfold R.v16484, N.v16484.
  rewrite ?node_27057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27059 (s : N.State) (i : N.Inputs) :
  R.v27059 (state s) (inputs i) = Zmod.unsigned (N.v27059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27059 s i)) at 1.
  unfold R.v27059, N.v27059.
  rewrite ?node_27054.
  rewrite ?node_27058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27060 (s : N.State) (i : N.Inputs) :
  R.v27060 (state s) (inputs i) = Zmod.unsigned (N.v27060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27060 s i)) at 1.
  unfold R.v27060, N.v27060.
  unfold R.v6, N.v6.
  rewrite ?node_27059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27061 (s : N.State) (i : N.Inputs) :
  R.v27061 (state s) (inputs i) = Zmod.unsigned (N.v27061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27061 s i)) at 1.
  unfold R.v27061, N.v27061.
  rewrite ?node_10345.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27062 (s : N.State) (i : N.Inputs) :
  R.v27062 (state s) (inputs i) = Zmod.unsigned (N.v27062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27062 s i)) at 1.
  unfold R.v27062, N.v27062.
  unfold R.v6, N.v6.
  rewrite ?node_10554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27063 (s : N.State) (i : N.Inputs) :
  R.v27063 (state s) (inputs i) = Zmod.unsigned (N.v27063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27063 s i)) at 1.
  unfold R.v27063, N.v27063.
  rewrite ?node_27061.
  rewrite ?node_27062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27064 (s : N.State) (i : N.Inputs) :
  R.v27064 (state s) (inputs i) = Zmod.unsigned (N.v27064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27064 s i)) at 1.
  unfold R.v27064, N.v27064.
  rewrite ?node_27060.
  rewrite ?node_27063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27065 (s : N.State) (i : N.Inputs) :
  R.v27065 (state s) (inputs i) = Zmod.unsigned (N.v27065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27065 s i)) at 1.
  unfold R.v27065, N.v27065.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27066 (s : N.State) (i : N.Inputs) :
  R.v27066 (state s) (inputs i) = Zmod.unsigned (N.v27066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27066 s i)) at 1.
  unfold R.v27066, N.v27066.
  unfold R.v6, N.v6.
  rewrite !state_r1153_nr_5F1153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1153_nr_5F1153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27067 (s : N.State) (i : N.Inputs) :
  R.v27067 (state s) (inputs i) = Zmod.unsigned (N.v27067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27067 s i)) at 1.
  unfold R.v27067, N.v27067.
  unfold R.v6, N.v6.
  rewrite !state_r1152_nr_5F1152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1152_nr_5F1152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27068 (s : N.State) (i : N.Inputs) :
  R.v27068 (state s) (inputs i) = Zmod.unsigned (N.v27068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27068 s i)) at 1.
  unfold R.v27068, N.v27068.
  rewrite ?node_27066.
  rewrite ?node_27067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27069 (s : N.State) (i : N.Inputs) :
  R.v27069 (state s) (inputs i) = Zmod.unsigned (N.v27069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27069 s i)) at 1.
  unfold R.v27069, N.v27069.
  unfold R.v16463, N.v16463.
  rewrite ?node_27068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27070 (s : N.State) (i : N.Inputs) :
  R.v27070 (state s) (inputs i) = Zmod.unsigned (N.v27070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27070 s i)) at 1.
  unfold R.v27070, N.v27070.
  rewrite ?node_10352.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27071 (s : N.State) (i : N.Inputs) :
  R.v27071 (state s) (inputs i) = Zmod.unsigned (N.v27071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27071 s i)) at 1.
  unfold R.v27071, N.v27071.
  unfold R.v6, N.v6.
  rewrite ?node_10555.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27072 (s : N.State) (i : N.Inputs) :
  R.v27072 (state s) (inputs i) = Zmod.unsigned (N.v27072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27072 s i)) at 1.
  unfold R.v27072, N.v27072.
  rewrite ?node_27070.
  rewrite ?node_27071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27073 (s : N.State) (i : N.Inputs) :
  R.v27073 (state s) (inputs i) = Zmod.unsigned (N.v27073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27073 s i)) at 1.
  unfold R.v27073, N.v27073.
  rewrite ?node_27069.
  rewrite ?node_27072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27074 (s : N.State) (i : N.Inputs) :
  R.v27074 (state s) (inputs i) = Zmod.unsigned (N.v27074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27074 s i)) at 1.
  unfold R.v27074, N.v27074.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27075 (s : N.State) (i : N.Inputs) :
  R.v27075 (state s) (inputs i) = Zmod.unsigned (N.v27075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27075 s i)) at 1.
  unfold R.v27075, N.v27075.
  rewrite ?node_10444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27076 (s : N.State) (i : N.Inputs) :
  R.v27076 (state s) (inputs i) = Zmod.unsigned (N.v27076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27076 s i)) at 1.
  unfold R.v27076, N.v27076.
  unfold R.v16463, N.v16463.
  rewrite !state_r1157_nr_5F1157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1157_nr_5F1157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27077 (s : N.State) (i : N.Inputs) :
  R.v27077 (state s) (inputs i) = Zmod.unsigned (N.v27077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27077 s i)) at 1.
  unfold R.v27077, N.v27077.
  unfold R.v16463, N.v16463.
  rewrite !state_r1156_nr_5F1156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1156_nr_5F1156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27078 (s : N.State) (i : N.Inputs) :
  R.v27078 (state s) (inputs i) = Zmod.unsigned (N.v27078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27078 s i)) at 1.
  unfold R.v27078, N.v27078.
  unfold R.v6, N.v6.
  rewrite !state_r1155_nr_5F1155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1155_nr_5F1155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27079 (s : N.State) (i : N.Inputs) :
  R.v27079 (state s) (inputs i) = Zmod.unsigned (N.v27079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27079 s i)) at 1.
  unfold R.v27079, N.v27079.
  unfold R.v6, N.v6.
  rewrite !state_r1154_nr_5F1154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1154_nr_5F1154 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27080 (s : N.State) (i : N.Inputs) :
  R.v27080 (state s) (inputs i) = Zmod.unsigned (N.v27080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27080 s i)) at 1.
  unfold R.v27080, N.v27080.
  rewrite ?node_27078.
  rewrite ?node_27079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27081 (s : N.State) (i : N.Inputs) :
  R.v27081 (state s) (inputs i) = Zmod.unsigned (N.v27081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27081 s i)) at 1.
  unfold R.v27081, N.v27081.
  unfold R.v16484, N.v16484.
  rewrite ?node_27080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27082 (s : N.State) (i : N.Inputs) :
  R.v27082 (state s) (inputs i) = Zmod.unsigned (N.v27082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27082 s i)) at 1.
  unfold R.v27082, N.v27082.
  rewrite ?node_27075.
  rewrite ?node_27076.
  rewrite ?node_27077.
  rewrite ?node_27081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27083 (s : N.State) (i : N.Inputs) :
  R.v27083 (state s) (inputs i) = Zmod.unsigned (N.v27083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27083 s i)) at 1.
  unfold R.v27083, N.v27083.
  unfold R.v6, N.v6.
  rewrite ?node_27082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27084 (s : N.State) (i : N.Inputs) :
  R.v27084 (state s) (inputs i) = Zmod.unsigned (N.v27084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27084 s i)) at 1.
  unfold R.v27084, N.v27084.
  rewrite ?node_10445.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27085 (s : N.State) (i : N.Inputs) :
  R.v27085 (state s) (inputs i) = Zmod.unsigned (N.v27085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27085 s i)) at 1.
  unfold R.v27085, N.v27085.
  unfold R.v6, N.v6.
  rewrite ?node_10604.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27086 (s : N.State) (i : N.Inputs) :
  R.v27086 (state s) (inputs i) = Zmod.unsigned (N.v27086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27086 s i)) at 1.
  unfold R.v27086, N.v27086.
  unfold R.v6, N.v6.
  rewrite ?node_10672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27087 (s : N.State) (i : N.Inputs) :
  R.v27087 (state s) (inputs i) = Zmod.unsigned (N.v27087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27087 s i)) at 1.
  unfold R.v27087, N.v27087.
  rewrite ?node_27084.
  rewrite ?node_27085.
  rewrite ?node_27086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27088 (s : N.State) (i : N.Inputs) :
  R.v27088 (state s) (inputs i) = Zmod.unsigned (N.v27088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27088 s i)) at 1.
  unfold R.v27088, N.v27088.
  rewrite ?node_27083.
  rewrite ?node_27087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27089 (s : N.State) (i : N.Inputs) :
  R.v27089 (state s) (inputs i) = Zmod.unsigned (N.v27089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27089 s i)) at 1.
  unfold R.v27089, N.v27089.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27090 (s : N.State) (i : N.Inputs) :
  R.v27090 (state s) (inputs i) = Zmod.unsigned (N.v27090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27090 s i)) at 1.
  unfold R.v27090, N.v27090.
  unfold R.v16463, N.v16463.
  rewrite !state_r1156_nr_5F1156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1156_nr_5F1156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27091 (s : N.State) (i : N.Inputs) :
  R.v27091 (state s) (inputs i) = Zmod.unsigned (N.v27091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27091 s i)) at 1.
  unfold R.v27091, N.v27091.
  unfold R.v6, N.v6.
  rewrite !state_r1155_nr_5F1155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1155_nr_5F1155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27092 (s : N.State) (i : N.Inputs) :
  R.v27092 (state s) (inputs i) = Zmod.unsigned (N.v27092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27092 s i)) at 1.
  unfold R.v27092, N.v27092.
  unfold R.v6, N.v6.
  rewrite !state_r1154_nr_5F1154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1154_nr_5F1154 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27093 (s : N.State) (i : N.Inputs) :
  R.v27093 (state s) (inputs i) = Zmod.unsigned (N.v27093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27093 s i)) at 1.
  unfold R.v27093, N.v27093.
  rewrite ?node_27091.
  rewrite ?node_27092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27094 (s : N.State) (i : N.Inputs) :
  R.v27094 (state s) (inputs i) = Zmod.unsigned (N.v27094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27094 s i)) at 1.
  unfold R.v27094, N.v27094.
  unfold R.v16484, N.v16484.
  rewrite ?node_27093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27095 (s : N.State) (i : N.Inputs) :
  R.v27095 (state s) (inputs i) = Zmod.unsigned (N.v27095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27095 s i)) at 1.
  unfold R.v27095, N.v27095.
  rewrite ?node_27090.
  rewrite ?node_27094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27096 (s : N.State) (i : N.Inputs) :
  R.v27096 (state s) (inputs i) = Zmod.unsigned (N.v27096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27096 s i)) at 1.
  unfold R.v27096, N.v27096.
  unfold R.v6, N.v6.
  rewrite ?node_27095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27097 (s : N.State) (i : N.Inputs) :
  R.v27097 (state s) (inputs i) = Zmod.unsigned (N.v27097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27097 s i)) at 1.
  unfold R.v27097, N.v27097.
  rewrite ?node_10440.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27098 (s : N.State) (i : N.Inputs) :
  R.v27098 (state s) (inputs i) = Zmod.unsigned (N.v27098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27098 s i)) at 1.
  unfold R.v27098, N.v27098.
  unfold R.v6, N.v6.
  rewrite ?node_10604.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27099 (s : N.State) (i : N.Inputs) :
  R.v27099 (state s) (inputs i) = Zmod.unsigned (N.v27099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27099 s i)) at 1.
  unfold R.v27099, N.v27099.
  rewrite ?node_27097.
  rewrite ?node_27098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27100 (s : N.State) (i : N.Inputs) :
  R.v27100 (state s) (inputs i) = Zmod.unsigned (N.v27100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27100 s i)) at 1.
  unfold R.v27100, N.v27100.
  rewrite ?node_27096.
  rewrite ?node_27099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27101 (s : N.State) (i : N.Inputs) :
  R.v27101 (state s) (inputs i) = Zmod.unsigned (N.v27101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27101 s i)) at 1.
  unfold R.v27101, N.v27101.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27102 (s : N.State) (i : N.Inputs) :
  R.v27102 (state s) (inputs i) = Zmod.unsigned (N.v27102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27102 s i)) at 1.
  unfold R.v27102, N.v27102.
  rewrite ?node_10444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27103 (s : N.State) (i : N.Inputs) :
  R.v27103 (state s) (inputs i) = Zmod.unsigned (N.v27103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27103 s i)) at 1.
  unfold R.v27103, N.v27103.
  unfold R.v6, N.v6.
  rewrite !state_r1157_nr_5F1157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1157_nr_5F1157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27104 (s : N.State) (i : N.Inputs) :
  R.v27104 (state s) (inputs i) = Zmod.unsigned (N.v27104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27104 s i)) at 1.
  unfold R.v27104, N.v27104.
  unfold R.v6, N.v6.
  rewrite ?node_10440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27105 (s : N.State) (i : N.Inputs) :
  R.v27105 (state s) (inputs i) = Zmod.unsigned (N.v27105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27105 s i)) at 1.
  unfold R.v27105, N.v27105.
  rewrite ?node_27103.
  rewrite ?node_27104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27106 (s : N.State) (i : N.Inputs) :
  R.v27106 (state s) (inputs i) = Zmod.unsigned (N.v27106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27106 s i)) at 1.
  unfold R.v27106, N.v27106.
  unfold R.v16484, N.v16484.
  rewrite ?node_27105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27107 (s : N.State) (i : N.Inputs) :
  R.v27107 (state s) (inputs i) = Zmod.unsigned (N.v27107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27107 s i)) at 1.
  unfold R.v27107, N.v27107.
  rewrite ?node_27102.
  rewrite ?node_27106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27108 (s : N.State) (i : N.Inputs) :
  R.v27108 (state s) (inputs i) = Zmod.unsigned (N.v27108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27108 s i)) at 1.
  unfold R.v27108, N.v27108.
  unfold R.v6, N.v6.
  rewrite ?node_27107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27109 (s : N.State) (i : N.Inputs) :
  R.v27109 (state s) (inputs i) = Zmod.unsigned (N.v27109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27109 s i)) at 1.
  unfold R.v27109, N.v27109.
  rewrite ?node_10445.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27110 (s : N.State) (i : N.Inputs) :
  R.v27110 (state s) (inputs i) = Zmod.unsigned (N.v27110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27110 s i)) at 1.
  unfold R.v27110, N.v27110.
  unfold R.v6, N.v6.
  rewrite ?node_10672.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27111 (s : N.State) (i : N.Inputs) :
  R.v27111 (state s) (inputs i) = Zmod.unsigned (N.v27111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27111 s i)) at 1.
  unfold R.v27111, N.v27111.
  rewrite ?node_27109.
  rewrite ?node_27110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27112 (s : N.State) (i : N.Inputs) :
  R.v27112 (state s) (inputs i) = Zmod.unsigned (N.v27112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27112 s i)) at 1.
  unfold R.v27112, N.v27112.
  rewrite ?node_27108.
  rewrite ?node_27111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27113 (s : N.State) (i : N.Inputs) :
  R.v27113 (state s) (inputs i) = Zmod.unsigned (N.v27113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27113 s i)) at 1.
  unfold R.v27113, N.v27113.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27114 (s : N.State) (i : N.Inputs) :
  R.v27114 (state s) (inputs i) = Zmod.unsigned (N.v27114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27114 s i)) at 1.
  unfold R.v27114, N.v27114.
  rewrite ?node_10451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27115 (s : N.State) (i : N.Inputs) :
  R.v27115 (state s) (inputs i) = Zmod.unsigned (N.v27115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27115 s i)) at 1.
  unfold R.v27115, N.v27115.
  unfold R.v16463, N.v16463.
  rewrite !state_r1161_nr_5F1161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1161_nr_5F1161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27116 (s : N.State) (i : N.Inputs) :
  R.v27116 (state s) (inputs i) = Zmod.unsigned (N.v27116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27116 s i)) at 1.
  unfold R.v27116, N.v27116.
  unfold R.v16463, N.v16463.
  rewrite !state_r1160_nr_5F1160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1160_nr_5F1160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27117 (s : N.State) (i : N.Inputs) :
  R.v27117 (state s) (inputs i) = Zmod.unsigned (N.v27117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27117 s i)) at 1.
  unfold R.v27117, N.v27117.
  unfold R.v6, N.v6.
  rewrite !state_r1159_nr_5F1159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1159_nr_5F1159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27118 (s : N.State) (i : N.Inputs) :
  R.v27118 (state s) (inputs i) = Zmod.unsigned (N.v27118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27118 s i)) at 1.
  unfold R.v27118, N.v27118.
  unfold R.v6, N.v6.
  rewrite !state_r1158_nr_5F1158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1158_nr_5F1158 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27119 (s : N.State) (i : N.Inputs) :
  R.v27119 (state s) (inputs i) = Zmod.unsigned (N.v27119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27119 s i)) at 1.
  unfold R.v27119, N.v27119.
  rewrite ?node_27117.
  rewrite ?node_27118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27120 (s : N.State) (i : N.Inputs) :
  R.v27120 (state s) (inputs i) = Zmod.unsigned (N.v27120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27120 s i)) at 1.
  unfold R.v27120, N.v27120.
  unfold R.v16484, N.v16484.
  rewrite ?node_27119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27121 (s : N.State) (i : N.Inputs) :
  R.v27121 (state s) (inputs i) = Zmod.unsigned (N.v27121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27121 s i)) at 1.
  unfold R.v27121, N.v27121.
  rewrite ?node_27114.
  rewrite ?node_27115.
  rewrite ?node_27116.
  rewrite ?node_27120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27122 (s : N.State) (i : N.Inputs) :
  R.v27122 (state s) (inputs i) = Zmod.unsigned (N.v27122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27122 s i)) at 1.
  unfold R.v27122, N.v27122.
  unfold R.v6, N.v6.
  rewrite ?node_27121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27123 (s : N.State) (i : N.Inputs) :
  R.v27123 (state s) (inputs i) = Zmod.unsigned (N.v27123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27123 s i)) at 1.
  unfold R.v27123, N.v27123.
  rewrite ?node_10452.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27124 (s : N.State) (i : N.Inputs) :
  R.v27124 (state s) (inputs i) = Zmod.unsigned (N.v27124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27124 s i)) at 1.
  unfold R.v27124, N.v27124.
  unfold R.v6, N.v6.
  rewrite ?node_10611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27125 (s : N.State) (i : N.Inputs) :
  R.v27125 (state s) (inputs i) = Zmod.unsigned (N.v27125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27125 s i)) at 1.
  unfold R.v27125, N.v27125.
  unfold R.v6, N.v6.
  rewrite ?node_10676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27126 (s : N.State) (i : N.Inputs) :
  R.v27126 (state s) (inputs i) = Zmod.unsigned (N.v27126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27126 s i)) at 1.
  unfold R.v27126, N.v27126.
  rewrite ?node_27123.
  rewrite ?node_27124.
  rewrite ?node_27125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27127 (s : N.State) (i : N.Inputs) :
  R.v27127 (state s) (inputs i) = Zmod.unsigned (N.v27127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27127 s i)) at 1.
  unfold R.v27127, N.v27127.
  rewrite ?node_27122.
  rewrite ?node_27126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27128 (s : N.State) (i : N.Inputs) :
  R.v27128 (state s) (inputs i) = Zmod.unsigned (N.v27128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27128 s i)) at 1.
  unfold R.v27128, N.v27128.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27129 (s : N.State) (i : N.Inputs) :
  R.v27129 (state s) (inputs i) = Zmod.unsigned (N.v27129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27129 s i)) at 1.
  unfold R.v27129, N.v27129.
  unfold R.v16463, N.v16463.
  rewrite !state_r1160_nr_5F1160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1160_nr_5F1160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27130 (s : N.State) (i : N.Inputs) :
  R.v27130 (state s) (inputs i) = Zmod.unsigned (N.v27130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27130 s i)) at 1.
  unfold R.v27130, N.v27130.
  unfold R.v6, N.v6.
  rewrite !state_r1159_nr_5F1159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1159_nr_5F1159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27131 (s : N.State) (i : N.Inputs) :
  R.v27131 (state s) (inputs i) = Zmod.unsigned (N.v27131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27131 s i)) at 1.
  unfold R.v27131, N.v27131.
  unfold R.v6, N.v6.
  rewrite !state_r1158_nr_5F1158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1158_nr_5F1158 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27132 (s : N.State) (i : N.Inputs) :
  R.v27132 (state s) (inputs i) = Zmod.unsigned (N.v27132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27132 s i)) at 1.
  unfold R.v27132, N.v27132.
  rewrite ?node_27130.
  rewrite ?node_27131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27133 (s : N.State) (i : N.Inputs) :
  R.v27133 (state s) (inputs i) = Zmod.unsigned (N.v27133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27133 s i)) at 1.
  unfold R.v27133, N.v27133.
  unfold R.v16484, N.v16484.
  rewrite ?node_27132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27134 (s : N.State) (i : N.Inputs) :
  R.v27134 (state s) (inputs i) = Zmod.unsigned (N.v27134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27134 s i)) at 1.
  unfold R.v27134, N.v27134.
  rewrite ?node_27129.
  rewrite ?node_27133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27135 (s : N.State) (i : N.Inputs) :
  R.v27135 (state s) (inputs i) = Zmod.unsigned (N.v27135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27135 s i)) at 1.
  unfold R.v27135, N.v27135.
  unfold R.v6, N.v6.
  rewrite ?node_27134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27136 (s : N.State) (i : N.Inputs) :
  R.v27136 (state s) (inputs i) = Zmod.unsigned (N.v27136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27136 s i)) at 1.
  unfold R.v27136, N.v27136.
  rewrite ?node_10447.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27137 (s : N.State) (i : N.Inputs) :
  R.v27137 (state s) (inputs i) = Zmod.unsigned (N.v27137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27137 s i)) at 1.
  unfold R.v27137, N.v27137.
  unfold R.v6, N.v6.
  rewrite ?node_10611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27138 (s : N.State) (i : N.Inputs) :
  R.v27138 (state s) (inputs i) = Zmod.unsigned (N.v27138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27138 s i)) at 1.
  unfold R.v27138, N.v27138.
  rewrite ?node_27136.
  rewrite ?node_27137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27139 (s : N.State) (i : N.Inputs) :
  R.v27139 (state s) (inputs i) = Zmod.unsigned (N.v27139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27139 s i)) at 1.
  unfold R.v27139, N.v27139.
  rewrite ?node_27135.
  rewrite ?node_27138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27140 (s : N.State) (i : N.Inputs) :
  R.v27140 (state s) (inputs i) = Zmod.unsigned (N.v27140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27140 s i)) at 1.
  unfold R.v27140, N.v27140.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27141 (s : N.State) (i : N.Inputs) :
  R.v27141 (state s) (inputs i) = Zmod.unsigned (N.v27141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27141 s i)) at 1.
  unfold R.v27141, N.v27141.
  rewrite ?node_10451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27142 (s : N.State) (i : N.Inputs) :
  R.v27142 (state s) (inputs i) = Zmod.unsigned (N.v27142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27142 s i)) at 1.
  unfold R.v27142, N.v27142.
  unfold R.v6, N.v6.
  rewrite !state_r1161_nr_5F1161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1161_nr_5F1161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27143 (s : N.State) (i : N.Inputs) :
  R.v27143 (state s) (inputs i) = Zmod.unsigned (N.v27143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27143 s i)) at 1.
  unfold R.v27143, N.v27143.
  unfold R.v6, N.v6.
  rewrite ?node_10447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27144 (s : N.State) (i : N.Inputs) :
  R.v27144 (state s) (inputs i) = Zmod.unsigned (N.v27144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27144 s i)) at 1.
  unfold R.v27144, N.v27144.
  rewrite ?node_27142.
  rewrite ?node_27143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27145 (s : N.State) (i : N.Inputs) :
  R.v27145 (state s) (inputs i) = Zmod.unsigned (N.v27145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27145 s i)) at 1.
  unfold R.v27145, N.v27145.
  unfold R.v16484, N.v16484.
  rewrite ?node_27144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27146 (s : N.State) (i : N.Inputs) :
  R.v27146 (state s) (inputs i) = Zmod.unsigned (N.v27146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27146 s i)) at 1.
  unfold R.v27146, N.v27146.
  rewrite ?node_27141.
  rewrite ?node_27145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27147 (s : N.State) (i : N.Inputs) :
  R.v27147 (state s) (inputs i) = Zmod.unsigned (N.v27147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27147 s i)) at 1.
  unfold R.v27147, N.v27147.
  unfold R.v6, N.v6.
  rewrite ?node_27146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27148 (s : N.State) (i : N.Inputs) :
  R.v27148 (state s) (inputs i) = Zmod.unsigned (N.v27148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27148 s i)) at 1.
  unfold R.v27148, N.v27148.
  rewrite ?node_10452.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27149 (s : N.State) (i : N.Inputs) :
  R.v27149 (state s) (inputs i) = Zmod.unsigned (N.v27149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27149 s i)) at 1.
  unfold R.v27149, N.v27149.
  unfold R.v6, N.v6.
  rewrite ?node_10676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27150 (s : N.State) (i : N.Inputs) :
  R.v27150 (state s) (inputs i) = Zmod.unsigned (N.v27150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27150 s i)) at 1.
  unfold R.v27150, N.v27150.
  rewrite ?node_27148.
  rewrite ?node_27149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27151 (s : N.State) (i : N.Inputs) :
  R.v27151 (state s) (inputs i) = Zmod.unsigned (N.v27151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27151 s i)) at 1.
  unfold R.v27151, N.v27151.
  rewrite ?node_27147.
  rewrite ?node_27150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27152 (s : N.State) (i : N.Inputs) :
  R.v27152 (state s) (inputs i) = Zmod.unsigned (N.v27152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27152 s i)) at 1.
  unfold R.v27152, N.v27152.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27153 (s : N.State) (i : N.Inputs) :
  R.v27153 (state s) (inputs i) = Zmod.unsigned (N.v27153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27153 s i)) at 1.
  unfold R.v27153, N.v27153.
  rewrite ?node_10459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27154 (s : N.State) (i : N.Inputs) :
  R.v27154 (state s) (inputs i) = Zmod.unsigned (N.v27154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27154 s i)) at 1.
  unfold R.v27154, N.v27154.
  unfold R.v16463, N.v16463.
  rewrite !state_r1165_nr_5F1165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1165_nr_5F1165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27155 (s : N.State) (i : N.Inputs) :
  R.v27155 (state s) (inputs i) = Zmod.unsigned (N.v27155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27155 s i)) at 1.
  unfold R.v27155, N.v27155.
  unfold R.v16463, N.v16463.
  rewrite !state_r1164_nr_5F1164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1164_nr_5F1164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27156 (s : N.State) (i : N.Inputs) :
  R.v27156 (state s) (inputs i) = Zmod.unsigned (N.v27156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27156 s i)) at 1.
  unfold R.v27156, N.v27156.
  unfold R.v6, N.v6.
  rewrite !state_r1163_nr_5F1163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1163_nr_5F1163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27157 (s : N.State) (i : N.Inputs) :
  R.v27157 (state s) (inputs i) = Zmod.unsigned (N.v27157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27157 s i)) at 1.
  unfold R.v27157, N.v27157.
  unfold R.v6, N.v6.
  rewrite !state_r1162_nr_5F1162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1162_nr_5F1162 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27158 (s : N.State) (i : N.Inputs) :
  R.v27158 (state s) (inputs i) = Zmod.unsigned (N.v27158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27158 s i)) at 1.
  unfold R.v27158, N.v27158.
  rewrite ?node_27156.
  rewrite ?node_27157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27159 (s : N.State) (i : N.Inputs) :
  R.v27159 (state s) (inputs i) = Zmod.unsigned (N.v27159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27159 s i)) at 1.
  unfold R.v27159, N.v27159.
  unfold R.v16484, N.v16484.
  rewrite ?node_27158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27160 (s : N.State) (i : N.Inputs) :
  R.v27160 (state s) (inputs i) = Zmod.unsigned (N.v27160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27160 s i)) at 1.
  unfold R.v27160, N.v27160.
  rewrite ?node_27153.
  rewrite ?node_27154.
  rewrite ?node_27155.
  rewrite ?node_27159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27161 (s : N.State) (i : N.Inputs) :
  R.v27161 (state s) (inputs i) = Zmod.unsigned (N.v27161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27161 s i)) at 1.
  unfold R.v27161, N.v27161.
  unfold R.v6, N.v6.
  rewrite ?node_27160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27162 (s : N.State) (i : N.Inputs) :
  R.v27162 (state s) (inputs i) = Zmod.unsigned (N.v27162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27162 s i)) at 1.
  unfold R.v27162, N.v27162.
  rewrite ?node_10460.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27163 (s : N.State) (i : N.Inputs) :
  R.v27163 (state s) (inputs i) = Zmod.unsigned (N.v27163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27163 s i)) at 1.
  unfold R.v27163, N.v27163.
  unfold R.v6, N.v6.
  rewrite ?node_10619.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27164 (s : N.State) (i : N.Inputs) :
  R.v27164 (state s) (inputs i) = Zmod.unsigned (N.v27164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27164 s i)) at 1.
  unfold R.v27164, N.v27164.
  unfold R.v6, N.v6.
  rewrite ?node_10680.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27165 (s : N.State) (i : N.Inputs) :
  R.v27165 (state s) (inputs i) = Zmod.unsigned (N.v27165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27165 s i)) at 1.
  unfold R.v27165, N.v27165.
  rewrite ?node_27162.
  rewrite ?node_27163.
  rewrite ?node_27164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27166 (s : N.State) (i : N.Inputs) :
  R.v27166 (state s) (inputs i) = Zmod.unsigned (N.v27166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27166 s i)) at 1.
  unfold R.v27166, N.v27166.
  rewrite ?node_27161.
  rewrite ?node_27165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27167 (s : N.State) (i : N.Inputs) :
  R.v27167 (state s) (inputs i) = Zmod.unsigned (N.v27167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27167 s i)) at 1.
  unfold R.v27167, N.v27167.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27168 (s : N.State) (i : N.Inputs) :
  R.v27168 (state s) (inputs i) = Zmod.unsigned (N.v27168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27168 s i)) at 1.
  unfold R.v27168, N.v27168.
  unfold R.v16463, N.v16463.
  rewrite !state_r1164_nr_5F1164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1164_nr_5F1164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27169 (s : N.State) (i : N.Inputs) :
  R.v27169 (state s) (inputs i) = Zmod.unsigned (N.v27169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27169 s i)) at 1.
  unfold R.v27169, N.v27169.
  unfold R.v6, N.v6.
  rewrite !state_r1163_nr_5F1163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1163_nr_5F1163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27170 (s : N.State) (i : N.Inputs) :
  R.v27170 (state s) (inputs i) = Zmod.unsigned (N.v27170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27170 s i)) at 1.
  unfold R.v27170, N.v27170.
  unfold R.v6, N.v6.
  rewrite !state_r1162_nr_5F1162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1162_nr_5F1162 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27171 (s : N.State) (i : N.Inputs) :
  R.v27171 (state s) (inputs i) = Zmod.unsigned (N.v27171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27171 s i)) at 1.
  unfold R.v27171, N.v27171.
  rewrite ?node_27169.
  rewrite ?node_27170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27172 (s : N.State) (i : N.Inputs) :
  R.v27172 (state s) (inputs i) = Zmod.unsigned (N.v27172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27172 s i)) at 1.
  unfold R.v27172, N.v27172.
  unfold R.v16484, N.v16484.
  rewrite ?node_27171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27173 (s : N.State) (i : N.Inputs) :
  R.v27173 (state s) (inputs i) = Zmod.unsigned (N.v27173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27173 s i)) at 1.
  unfold R.v27173, N.v27173.
  rewrite ?node_27168.
  rewrite ?node_27172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27174 (s : N.State) (i : N.Inputs) :
  R.v27174 (state s) (inputs i) = Zmod.unsigned (N.v27174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27174 s i)) at 1.
  unfold R.v27174, N.v27174.
  unfold R.v6, N.v6.
  rewrite ?node_27173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27175 (s : N.State) (i : N.Inputs) :
  R.v27175 (state s) (inputs i) = Zmod.unsigned (N.v27175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27175 s i)) at 1.
  unfold R.v27175, N.v27175.
  rewrite ?node_10455.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27176 (s : N.State) (i : N.Inputs) :
  R.v27176 (state s) (inputs i) = Zmod.unsigned (N.v27176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27176 s i)) at 1.
  unfold R.v27176, N.v27176.
  unfold R.v6, N.v6.
  rewrite ?node_10619.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27177 (s : N.State) (i : N.Inputs) :
  R.v27177 (state s) (inputs i) = Zmod.unsigned (N.v27177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27177 s i)) at 1.
  unfold R.v27177, N.v27177.
  rewrite ?node_27175.
  rewrite ?node_27176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27178 (s : N.State) (i : N.Inputs) :
  R.v27178 (state s) (inputs i) = Zmod.unsigned (N.v27178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27178 s i)) at 1.
  unfold R.v27178, N.v27178.
  rewrite ?node_27174.
  rewrite ?node_27177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27179 (s : N.State) (i : N.Inputs) :
  R.v27179 (state s) (inputs i) = Zmod.unsigned (N.v27179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27179 s i)) at 1.
  unfold R.v27179, N.v27179.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27180 (s : N.State) (i : N.Inputs) :
  R.v27180 (state s) (inputs i) = Zmod.unsigned (N.v27180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27180 s i)) at 1.
  unfold R.v27180, N.v27180.
  rewrite ?node_10459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27181 (s : N.State) (i : N.Inputs) :
  R.v27181 (state s) (inputs i) = Zmod.unsigned (N.v27181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27181 s i)) at 1.
  unfold R.v27181, N.v27181.
  unfold R.v6, N.v6.
  rewrite !state_r1165_nr_5F1165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1165_nr_5F1165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27182 (s : N.State) (i : N.Inputs) :
  R.v27182 (state s) (inputs i) = Zmod.unsigned (N.v27182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27182 s i)) at 1.
  unfold R.v27182, N.v27182.
  unfold R.v6, N.v6.
  rewrite ?node_10455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27183 (s : N.State) (i : N.Inputs) :
  R.v27183 (state s) (inputs i) = Zmod.unsigned (N.v27183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27183 s i)) at 1.
  unfold R.v27183, N.v27183.
  rewrite ?node_27181.
  rewrite ?node_27182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27184 (s : N.State) (i : N.Inputs) :
  R.v27184 (state s) (inputs i) = Zmod.unsigned (N.v27184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27184 s i)) at 1.
  unfold R.v27184, N.v27184.
  unfold R.v16484, N.v16484.
  rewrite ?node_27183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27185 (s : N.State) (i : N.Inputs) :
  R.v27185 (state s) (inputs i) = Zmod.unsigned (N.v27185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27185 s i)) at 1.
  unfold R.v27185, N.v27185.
  rewrite ?node_27180.
  rewrite ?node_27184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27186 (s : N.State) (i : N.Inputs) :
  R.v27186 (state s) (inputs i) = Zmod.unsigned (N.v27186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27186 s i)) at 1.
  unfold R.v27186, N.v27186.
  unfold R.v6, N.v6.
  rewrite ?node_27185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27187 (s : N.State) (i : N.Inputs) :
  R.v27187 (state s) (inputs i) = Zmod.unsigned (N.v27187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27187 s i)) at 1.
  unfold R.v27187, N.v27187.
  rewrite ?node_10460.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27188 (s : N.State) (i : N.Inputs) :
  R.v27188 (state s) (inputs i) = Zmod.unsigned (N.v27188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27188 s i)) at 1.
  unfold R.v27188, N.v27188.
  unfold R.v6, N.v6.
  rewrite ?node_10680.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27189 (s : N.State) (i : N.Inputs) :
  R.v27189 (state s) (inputs i) = Zmod.unsigned (N.v27189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27189 s i)) at 1.
  unfold R.v27189, N.v27189.
  rewrite ?node_27187.
  rewrite ?node_27188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27190 (s : N.State) (i : N.Inputs) :
  R.v27190 (state s) (inputs i) = Zmod.unsigned (N.v27190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27190 s i)) at 1.
  unfold R.v27190, N.v27190.
  rewrite ?node_27186.
  rewrite ?node_27189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27191 (s : N.State) (i : N.Inputs) :
  R.v27191 (state s) (inputs i) = Zmod.unsigned (N.v27191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27191 s i)) at 1.
  unfold R.v27191, N.v27191.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27192 (s : N.State) (i : N.Inputs) :
  R.v27192 (state s) (inputs i) = Zmod.unsigned (N.v27192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27192 s i)) at 1.
  unfold R.v27192, N.v27192.
  rewrite ?node_10467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27193 (s : N.State) (i : N.Inputs) :
  R.v27193 (state s) (inputs i) = Zmod.unsigned (N.v27193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27193 s i)) at 1.
  unfold R.v27193, N.v27193.
  unfold R.v16463, N.v16463.
  rewrite !state_r1169_nr_5F1169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1169_nr_5F1169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27194 (s : N.State) (i : N.Inputs) :
  R.v27194 (state s) (inputs i) = Zmod.unsigned (N.v27194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27194 s i)) at 1.
  unfold R.v27194, N.v27194.
  unfold R.v16463, N.v16463.
  rewrite !state_r1168_nr_5F1168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1168_nr_5F1168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27195 (s : N.State) (i : N.Inputs) :
  R.v27195 (state s) (inputs i) = Zmod.unsigned (N.v27195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27195 s i)) at 1.
  unfold R.v27195, N.v27195.
  unfold R.v6, N.v6.
  rewrite !state_r1167_nr_5F1167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1167_nr_5F1167 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27196 (s : N.State) (i : N.Inputs) :
  R.v27196 (state s) (inputs i) = Zmod.unsigned (N.v27196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27196 s i)) at 1.
  unfold R.v27196, N.v27196.
  unfold R.v6, N.v6.
  rewrite !state_r1166_nr_5F1166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1166_nr_5F1166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27197 (s : N.State) (i : N.Inputs) :
  R.v27197 (state s) (inputs i) = Zmod.unsigned (N.v27197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27197 s i)) at 1.
  unfold R.v27197, N.v27197.
  rewrite ?node_27195.
  rewrite ?node_27196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27198 (s : N.State) (i : N.Inputs) :
  R.v27198 (state s) (inputs i) = Zmod.unsigned (N.v27198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27198 s i)) at 1.
  unfold R.v27198, N.v27198.
  unfold R.v16484, N.v16484.
  rewrite ?node_27197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27199 (s : N.State) (i : N.Inputs) :
  R.v27199 (state s) (inputs i) = Zmod.unsigned (N.v27199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27199 s i)) at 1.
  unfold R.v27199, N.v27199.
  rewrite ?node_27192.
  rewrite ?node_27193.
  rewrite ?node_27194.
  rewrite ?node_27198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27200 (s : N.State) (i : N.Inputs) :
  R.v27200 (state s) (inputs i) = Zmod.unsigned (N.v27200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27200 s i)) at 1.
  unfold R.v27200, N.v27200.
  unfold R.v6, N.v6.
  rewrite ?node_27199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27201 (s : N.State) (i : N.Inputs) :
  R.v27201 (state s) (inputs i) = Zmod.unsigned (N.v27201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27201 s i)) at 1.
  unfold R.v27201, N.v27201.
  rewrite ?node_10468.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27202 (s : N.State) (i : N.Inputs) :
  R.v27202 (state s) (inputs i) = Zmod.unsigned (N.v27202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27202 s i)) at 1.
  unfold R.v27202, N.v27202.
  unfold R.v6, N.v6.
  rewrite ?node_10627.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27203 (s : N.State) (i : N.Inputs) :
  R.v27203 (state s) (inputs i) = Zmod.unsigned (N.v27203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27203 s i)) at 1.
  unfold R.v27203, N.v27203.
  unfold R.v6, N.v6.
  rewrite ?node_10689.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27204 (s : N.State) (i : N.Inputs) :
  R.v27204 (state s) (inputs i) = Zmod.unsigned (N.v27204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27204 s i)) at 1.
  unfold R.v27204, N.v27204.
  rewrite ?node_27201.
  rewrite ?node_27202.
  rewrite ?node_27203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27205 (s : N.State) (i : N.Inputs) :
  R.v27205 (state s) (inputs i) = Zmod.unsigned (N.v27205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27205 s i)) at 1.
  unfold R.v27205, N.v27205.
  rewrite ?node_27200.
  rewrite ?node_27204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27206 (s : N.State) (i : N.Inputs) :
  R.v27206 (state s) (inputs i) = Zmod.unsigned (N.v27206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27206 s i)) at 1.
  unfold R.v27206, N.v27206.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27207 (s : N.State) (i : N.Inputs) :
  R.v27207 (state s) (inputs i) = Zmod.unsigned (N.v27207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27207 s i)) at 1.
  unfold R.v27207, N.v27207.
  unfold R.v16463, N.v16463.
  rewrite !state_r1168_nr_5F1168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1168_nr_5F1168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27208 (s : N.State) (i : N.Inputs) :
  R.v27208 (state s) (inputs i) = Zmod.unsigned (N.v27208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27208 s i)) at 1.
  unfold R.v27208, N.v27208.
  unfold R.v6, N.v6.
  rewrite !state_r1167_nr_5F1167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1167_nr_5F1167 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27209 (s : N.State) (i : N.Inputs) :
  R.v27209 (state s) (inputs i) = Zmod.unsigned (N.v27209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27209 s i)) at 1.
  unfold R.v27209, N.v27209.
  unfold R.v6, N.v6.
  rewrite !state_r1166_nr_5F1166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1166_nr_5F1166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27210 (s : N.State) (i : N.Inputs) :
  R.v27210 (state s) (inputs i) = Zmod.unsigned (N.v27210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27210 s i)) at 1.
  unfold R.v27210, N.v27210.
  rewrite ?node_27208.
  rewrite ?node_27209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27211 (s : N.State) (i : N.Inputs) :
  R.v27211 (state s) (inputs i) = Zmod.unsigned (N.v27211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27211 s i)) at 1.
  unfold R.v27211, N.v27211.
  unfold R.v16484, N.v16484.
  rewrite ?node_27210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27212 (s : N.State) (i : N.Inputs) :
  R.v27212 (state s) (inputs i) = Zmod.unsigned (N.v27212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27212 s i)) at 1.
  unfold R.v27212, N.v27212.
  rewrite ?node_27207.
  rewrite ?node_27211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27213 (s : N.State) (i : N.Inputs) :
  R.v27213 (state s) (inputs i) = Zmod.unsigned (N.v27213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27213 s i)) at 1.
  unfold R.v27213, N.v27213.
  unfold R.v6, N.v6.
  rewrite ?node_27212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27214 (s : N.State) (i : N.Inputs) :
  R.v27214 (state s) (inputs i) = Zmod.unsigned (N.v27214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27214 s i)) at 1.
  unfold R.v27214, N.v27214.
  rewrite ?node_10463.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27215 (s : N.State) (i : N.Inputs) :
  R.v27215 (state s) (inputs i) = Zmod.unsigned (N.v27215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27215 s i)) at 1.
  unfold R.v27215, N.v27215.
  unfold R.v6, N.v6.
  rewrite ?node_10627.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27216 (s : N.State) (i : N.Inputs) :
  R.v27216 (state s) (inputs i) = Zmod.unsigned (N.v27216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27216 s i)) at 1.
  unfold R.v27216, N.v27216.
  rewrite ?node_27214.
  rewrite ?node_27215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27217 (s : N.State) (i : N.Inputs) :
  R.v27217 (state s) (inputs i) = Zmod.unsigned (N.v27217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27217 s i)) at 1.
  unfold R.v27217, N.v27217.
  rewrite ?node_27213.
  rewrite ?node_27216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27218 (s : N.State) (i : N.Inputs) :
  R.v27218 (state s) (inputs i) = Zmod.unsigned (N.v27218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27218 s i)) at 1.
  unfold R.v27218, N.v27218.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27219 (s : N.State) (i : N.Inputs) :
  R.v27219 (state s) (inputs i) = Zmod.unsigned (N.v27219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27219 s i)) at 1.
  unfold R.v27219, N.v27219.
  rewrite ?node_10467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27220 (s : N.State) (i : N.Inputs) :
  R.v27220 (state s) (inputs i) = Zmod.unsigned (N.v27220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27220 s i)) at 1.
  unfold R.v27220, N.v27220.
  unfold R.v6, N.v6.
  rewrite !state_r1169_nr_5F1169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1169_nr_5F1169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27221 (s : N.State) (i : N.Inputs) :
  R.v27221 (state s) (inputs i) = Zmod.unsigned (N.v27221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27221 s i)) at 1.
  unfold R.v27221, N.v27221.
  unfold R.v6, N.v6.
  rewrite ?node_10463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27222 (s : N.State) (i : N.Inputs) :
  R.v27222 (state s) (inputs i) = Zmod.unsigned (N.v27222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27222 s i)) at 1.
  unfold R.v27222, N.v27222.
  rewrite ?node_27220.
  rewrite ?node_27221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27223 (s : N.State) (i : N.Inputs) :
  R.v27223 (state s) (inputs i) = Zmod.unsigned (N.v27223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27223 s i)) at 1.
  unfold R.v27223, N.v27223.
  unfold R.v16484, N.v16484.
  rewrite ?node_27222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27224 (s : N.State) (i : N.Inputs) :
  R.v27224 (state s) (inputs i) = Zmod.unsigned (N.v27224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27224 s i)) at 1.
  unfold R.v27224, N.v27224.
  rewrite ?node_27219.
  rewrite ?node_27223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27225 (s : N.State) (i : N.Inputs) :
  R.v27225 (state s) (inputs i) = Zmod.unsigned (N.v27225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27225 s i)) at 1.
  unfold R.v27225, N.v27225.
  unfold R.v6, N.v6.
  rewrite ?node_27224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27226 (s : N.State) (i : N.Inputs) :
  R.v27226 (state s) (inputs i) = Zmod.unsigned (N.v27226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27226 s i)) at 1.
  unfold R.v27226, N.v27226.
  rewrite ?node_10468.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27227 (s : N.State) (i : N.Inputs) :
  R.v27227 (state s) (inputs i) = Zmod.unsigned (N.v27227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27227 s i)) at 1.
  unfold R.v27227, N.v27227.
  unfold R.v6, N.v6.
  rewrite ?node_10689.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27228 (s : N.State) (i : N.Inputs) :
  R.v27228 (state s) (inputs i) = Zmod.unsigned (N.v27228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27228 s i)) at 1.
  unfold R.v27228, N.v27228.
  rewrite ?node_27226.
  rewrite ?node_27227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27229 (s : N.State) (i : N.Inputs) :
  R.v27229 (state s) (inputs i) = Zmod.unsigned (N.v27229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27229 s i)) at 1.
  unfold R.v27229, N.v27229.
  rewrite ?node_27225.
  rewrite ?node_27228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27230 (s : N.State) (i : N.Inputs) :
  R.v27230 (state s) (inputs i) = Zmod.unsigned (N.v27230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27230 s i)) at 1.
  unfold R.v27230, N.v27230.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27231 (s : N.State) (i : N.Inputs) :
  R.v27231 (state s) (inputs i) = Zmod.unsigned (N.v27231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27231 s i)) at 1.
  unfold R.v27231, N.v27231.
  rewrite ?node_10479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27232 (s : N.State) (i : N.Inputs) :
  R.v27232 (state s) (inputs i) = Zmod.unsigned (N.v27232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27232 s i)) at 1.
  unfold R.v27232, N.v27232.
  unfold R.v16463, N.v16463.
  rewrite !state_r1173_nr_5F1173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1173_nr_5F1173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27233 (s : N.State) (i : N.Inputs) :
  R.v27233 (state s) (inputs i) = Zmod.unsigned (N.v27233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27233 s i)) at 1.
  unfold R.v27233, N.v27233.
  unfold R.v16463, N.v16463.
  rewrite !state_r1172_nr_5F1172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1172_nr_5F1172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27234 (s : N.State) (i : N.Inputs) :
  R.v27234 (state s) (inputs i) = Zmod.unsigned (N.v27234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27234 s i)) at 1.
  unfold R.v27234, N.v27234.
  unfold R.v6, N.v6.
  rewrite !state_r1171_nr_5F1171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1171_nr_5F1171 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27235 (s : N.State) (i : N.Inputs) :
  R.v27235 (state s) (inputs i) = Zmod.unsigned (N.v27235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27235 s i)) at 1.
  unfold R.v27235, N.v27235.
  unfold R.v6, N.v6.
  rewrite !state_r1170_nr_5F1170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1170_nr_5F1170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27236 (s : N.State) (i : N.Inputs) :
  R.v27236 (state s) (inputs i) = Zmod.unsigned (N.v27236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27236 s i)) at 1.
  unfold R.v27236, N.v27236.
  rewrite ?node_27234.
  rewrite ?node_27235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27237 (s : N.State) (i : N.Inputs) :
  R.v27237 (state s) (inputs i) = Zmod.unsigned (N.v27237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27237 s i)) at 1.
  unfold R.v27237, N.v27237.
  unfold R.v16484, N.v16484.
  rewrite ?node_27236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27238 (s : N.State) (i : N.Inputs) :
  R.v27238 (state s) (inputs i) = Zmod.unsigned (N.v27238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27238 s i)) at 1.
  unfold R.v27238, N.v27238.
  rewrite ?node_27231.
  rewrite ?node_27232.
  rewrite ?node_27233.
  rewrite ?node_27237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27239 (s : N.State) (i : N.Inputs) :
  R.v27239 (state s) (inputs i) = Zmod.unsigned (N.v27239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27239 s i)) at 1.
  unfold R.v27239, N.v27239.
  unfold R.v6, N.v6.
  rewrite ?node_27238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27240 (s : N.State) (i : N.Inputs) :
  R.v27240 (state s) (inputs i) = Zmod.unsigned (N.v27240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27240 s i)) at 1.
  unfold R.v27240, N.v27240.
  rewrite ?node_10480.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27241 (s : N.State) (i : N.Inputs) :
  R.v27241 (state s) (inputs i) = Zmod.unsigned (N.v27241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27241 s i)) at 1.
  unfold R.v27241, N.v27241.
  unfold R.v6, N.v6.
  rewrite ?node_10639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27242 (s : N.State) (i : N.Inputs) :
  R.v27242 (state s) (inputs i) = Zmod.unsigned (N.v27242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27242 s i)) at 1.
  unfold R.v27242, N.v27242.
  unfold R.v6, N.v6.
  rewrite ?node_10692.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27243 (s : N.State) (i : N.Inputs) :
  R.v27243 (state s) (inputs i) = Zmod.unsigned (N.v27243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27243 s i)) at 1.
  unfold R.v27243, N.v27243.
  rewrite ?node_27240.
  rewrite ?node_27241.
  rewrite ?node_27242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27244 (s : N.State) (i : N.Inputs) :
  R.v27244 (state s) (inputs i) = Zmod.unsigned (N.v27244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27244 s i)) at 1.
  unfold R.v27244, N.v27244.
  rewrite ?node_27239.
  rewrite ?node_27243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27245 (s : N.State) (i : N.Inputs) :
  R.v27245 (state s) (inputs i) = Zmod.unsigned (N.v27245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27245 s i)) at 1.
  unfold R.v27245, N.v27245.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27246 (s : N.State) (i : N.Inputs) :
  R.v27246 (state s) (inputs i) = Zmod.unsigned (N.v27246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27246 s i)) at 1.
  unfold R.v27246, N.v27246.
  unfold R.v16463, N.v16463.
  rewrite !state_r1172_nr_5F1172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1172_nr_5F1172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27247 (s : N.State) (i : N.Inputs) :
  R.v27247 (state s) (inputs i) = Zmod.unsigned (N.v27247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27247 s i)) at 1.
  unfold R.v27247, N.v27247.
  unfold R.v6, N.v6.
  rewrite !state_r1171_nr_5F1171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1171_nr_5F1171 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27248 (s : N.State) (i : N.Inputs) :
  R.v27248 (state s) (inputs i) = Zmod.unsigned (N.v27248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27248 s i)) at 1.
  unfold R.v27248, N.v27248.
  unfold R.v6, N.v6.
  rewrite !state_r1170_nr_5F1170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1170_nr_5F1170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27249 (s : N.State) (i : N.Inputs) :
  R.v27249 (state s) (inputs i) = Zmod.unsigned (N.v27249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27249 s i)) at 1.
  unfold R.v27249, N.v27249.
  rewrite ?node_27247.
  rewrite ?node_27248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27250 (s : N.State) (i : N.Inputs) :
  R.v27250 (state s) (inputs i) = Zmod.unsigned (N.v27250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27250 s i)) at 1.
  unfold R.v27250, N.v27250.
  unfold R.v16484, N.v16484.
  rewrite ?node_27249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27251 (s : N.State) (i : N.Inputs) :
  R.v27251 (state s) (inputs i) = Zmod.unsigned (N.v27251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27251 s i)) at 1.
  unfold R.v27251, N.v27251.
  rewrite ?node_27246.
  rewrite ?node_27250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27252 (s : N.State) (i : N.Inputs) :
  R.v27252 (state s) (inputs i) = Zmod.unsigned (N.v27252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27252 s i)) at 1.
  unfold R.v27252, N.v27252.
  unfold R.v6, N.v6.
  rewrite ?node_27251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27253 (s : N.State) (i : N.Inputs) :
  R.v27253 (state s) (inputs i) = Zmod.unsigned (N.v27253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27253 s i)) at 1.
  unfold R.v27253, N.v27253.
  rewrite ?node_10475.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27254 (s : N.State) (i : N.Inputs) :
  R.v27254 (state s) (inputs i) = Zmod.unsigned (N.v27254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27254 s i)) at 1.
  unfold R.v27254, N.v27254.
  unfold R.v6, N.v6.
  rewrite ?node_10639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27255 (s : N.State) (i : N.Inputs) :
  R.v27255 (state s) (inputs i) = Zmod.unsigned (N.v27255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27255 s i)) at 1.
  unfold R.v27255, N.v27255.
  rewrite ?node_27253.
  rewrite ?node_27254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27256 (s : N.State) (i : N.Inputs) :
  R.v27256 (state s) (inputs i) = Zmod.unsigned (N.v27256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27256 s i)) at 1.
  unfold R.v27256, N.v27256.
  rewrite ?node_27252.
  rewrite ?node_27255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27257 (s : N.State) (i : N.Inputs) :
  R.v27257 (state s) (inputs i) = Zmod.unsigned (N.v27257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27257 s i)) at 1.
  unfold R.v27257, N.v27257.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27258 (s : N.State) (i : N.Inputs) :
  R.v27258 (state s) (inputs i) = Zmod.unsigned (N.v27258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27258 s i)) at 1.
  unfold R.v27258, N.v27258.
  rewrite ?node_10479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27259 (s : N.State) (i : N.Inputs) :
  R.v27259 (state s) (inputs i) = Zmod.unsigned (N.v27259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27259 s i)) at 1.
  unfold R.v27259, N.v27259.
  unfold R.v6, N.v6.
  rewrite !state_r1173_nr_5F1173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1173_nr_5F1173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27260 (s : N.State) (i : N.Inputs) :
  R.v27260 (state s) (inputs i) = Zmod.unsigned (N.v27260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27260 s i)) at 1.
  unfold R.v27260, N.v27260.
  unfold R.v6, N.v6.
  rewrite ?node_10475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27261 (s : N.State) (i : N.Inputs) :
  R.v27261 (state s) (inputs i) = Zmod.unsigned (N.v27261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27261 s i)) at 1.
  unfold R.v27261, N.v27261.
  rewrite ?node_27259.
  rewrite ?node_27260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27262 (s : N.State) (i : N.Inputs) :
  R.v27262 (state s) (inputs i) = Zmod.unsigned (N.v27262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27262 s i)) at 1.
  unfold R.v27262, N.v27262.
  unfold R.v16484, N.v16484.
  rewrite ?node_27261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27263 (s : N.State) (i : N.Inputs) :
  R.v27263 (state s) (inputs i) = Zmod.unsigned (N.v27263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27263 s i)) at 1.
  unfold R.v27263, N.v27263.
  rewrite ?node_27258.
  rewrite ?node_27262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27264 (s : N.State) (i : N.Inputs) :
  R.v27264 (state s) (inputs i) = Zmod.unsigned (N.v27264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27264 s i)) at 1.
  unfold R.v27264, N.v27264.
  unfold R.v6, N.v6.
  rewrite ?node_27263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27265 (s : N.State) (i : N.Inputs) :
  R.v27265 (state s) (inputs i) = Zmod.unsigned (N.v27265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27265 s i)) at 1.
  unfold R.v27265, N.v27265.
  rewrite ?node_10480.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27266 (s : N.State) (i : N.Inputs) :
  R.v27266 (state s) (inputs i) = Zmod.unsigned (N.v27266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27266 s i)) at 1.
  unfold R.v27266, N.v27266.
  unfold R.v6, N.v6.
  rewrite ?node_10692.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27267 (s : N.State) (i : N.Inputs) :
  R.v27267 (state s) (inputs i) = Zmod.unsigned (N.v27267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27267 s i)) at 1.
  unfold R.v27267, N.v27267.
  rewrite ?node_27265.
  rewrite ?node_27266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27268 (s : N.State) (i : N.Inputs) :
  R.v27268 (state s) (inputs i) = Zmod.unsigned (N.v27268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27268 s i)) at 1.
  unfold R.v27268, N.v27268.
  rewrite ?node_27264.
  rewrite ?node_27267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27269 (s : N.State) (i : N.Inputs) :
  R.v27269 (state s) (inputs i) = Zmod.unsigned (N.v27269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27269 s i)) at 1.
  unfold R.v27269, N.v27269.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27270 (s : N.State) (i : N.Inputs) :
  R.v27270 (state s) (inputs i) = Zmod.unsigned (N.v27270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27270 s i)) at 1.
  unfold R.v27270, N.v27270.
  rewrite ?node_10486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27271 (s : N.State) (i : N.Inputs) :
  R.v27271 (state s) (inputs i) = Zmod.unsigned (N.v27271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27271 s i)) at 1.
  unfold R.v27271, N.v27271.
  unfold R.v16463, N.v16463.
  rewrite !state_r1177_nr_5F1177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1177_nr_5F1177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27272 (s : N.State) (i : N.Inputs) :
  R.v27272 (state s) (inputs i) = Zmod.unsigned (N.v27272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27272 s i)) at 1.
  unfold R.v27272, N.v27272.
  unfold R.v16463, N.v16463.
  rewrite !state_r1176_nr_5F1176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1176_nr_5F1176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27273 (s : N.State) (i : N.Inputs) :
  R.v27273 (state s) (inputs i) = Zmod.unsigned (N.v27273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27273 s i)) at 1.
  unfold R.v27273, N.v27273.
  unfold R.v6, N.v6.
  rewrite !state_r1175_nr_5F1175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1175_nr_5F1175 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27274 (s : N.State) (i : N.Inputs) :
  R.v27274 (state s) (inputs i) = Zmod.unsigned (N.v27274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27274 s i)) at 1.
  unfold R.v27274, N.v27274.
  unfold R.v6, N.v6.
  rewrite !state_r1174_nr_5F1174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1174_nr_5F1174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27275 (s : N.State) (i : N.Inputs) :
  R.v27275 (state s) (inputs i) = Zmod.unsigned (N.v27275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27275 s i)) at 1.
  unfold R.v27275, N.v27275.
  rewrite ?node_27273.
  rewrite ?node_27274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27276 (s : N.State) (i : N.Inputs) :
  R.v27276 (state s) (inputs i) = Zmod.unsigned (N.v27276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27276 s i)) at 1.
  unfold R.v27276, N.v27276.
  unfold R.v16484, N.v16484.
  rewrite ?node_27275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27277 (s : N.State) (i : N.Inputs) :
  R.v27277 (state s) (inputs i) = Zmod.unsigned (N.v27277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27277 s i)) at 1.
  unfold R.v27277, N.v27277.
  rewrite ?node_27270.
  rewrite ?node_27271.
  rewrite ?node_27272.
  rewrite ?node_27276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27278 (s : N.State) (i : N.Inputs) :
  R.v27278 (state s) (inputs i) = Zmod.unsigned (N.v27278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27278 s i)) at 1.
  unfold R.v27278, N.v27278.
  unfold R.v6, N.v6.
  rewrite ?node_27277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27279 (s : N.State) (i : N.Inputs) :
  R.v27279 (state s) (inputs i) = Zmod.unsigned (N.v27279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27279 s i)) at 1.
  unfold R.v27279, N.v27279.
  rewrite ?node_10487.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27280 (s : N.State) (i : N.Inputs) :
  R.v27280 (state s) (inputs i) = Zmod.unsigned (N.v27280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27280 s i)) at 1.
  unfold R.v27280, N.v27280.
  unfold R.v6, N.v6.
  rewrite ?node_10646.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27281 (s : N.State) (i : N.Inputs) :
  R.v27281 (state s) (inputs i) = Zmod.unsigned (N.v27281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27281 s i)) at 1.
  unfold R.v27281, N.v27281.
  unfold R.v6, N.v6.
  rewrite ?node_10696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27282 (s : N.State) (i : N.Inputs) :
  R.v27282 (state s) (inputs i) = Zmod.unsigned (N.v27282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27282 s i)) at 1.
  unfold R.v27282, N.v27282.
  rewrite ?node_27279.
  rewrite ?node_27280.
  rewrite ?node_27281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27283 (s : N.State) (i : N.Inputs) :
  R.v27283 (state s) (inputs i) = Zmod.unsigned (N.v27283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27283 s i)) at 1.
  unfold R.v27283, N.v27283.
  rewrite ?node_27278.
  rewrite ?node_27282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27284 (s : N.State) (i : N.Inputs) :
  R.v27284 (state s) (inputs i) = Zmod.unsigned (N.v27284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27284 s i)) at 1.
  unfold R.v27284, N.v27284.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27285 (s : N.State) (i : N.Inputs) :
  R.v27285 (state s) (inputs i) = Zmod.unsigned (N.v27285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27285 s i)) at 1.
  unfold R.v27285, N.v27285.
  unfold R.v16463, N.v16463.
  rewrite !state_r1176_nr_5F1176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1176_nr_5F1176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27286 (s : N.State) (i : N.Inputs) :
  R.v27286 (state s) (inputs i) = Zmod.unsigned (N.v27286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27286 s i)) at 1.
  unfold R.v27286, N.v27286.
  unfold R.v6, N.v6.
  rewrite !state_r1175_nr_5F1175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1175_nr_5F1175 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27287 (s : N.State) (i : N.Inputs) :
  R.v27287 (state s) (inputs i) = Zmod.unsigned (N.v27287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27287 s i)) at 1.
  unfold R.v27287, N.v27287.
  unfold R.v6, N.v6.
  rewrite !state_r1174_nr_5F1174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1174_nr_5F1174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27288 (s : N.State) (i : N.Inputs) :
  R.v27288 (state s) (inputs i) = Zmod.unsigned (N.v27288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27288 s i)) at 1.
  unfold R.v27288, N.v27288.
  rewrite ?node_27286.
  rewrite ?node_27287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27289 (s : N.State) (i : N.Inputs) :
  R.v27289 (state s) (inputs i) = Zmod.unsigned (N.v27289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27289 s i)) at 1.
  unfold R.v27289, N.v27289.
  unfold R.v16484, N.v16484.
  rewrite ?node_27288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27290 (s : N.State) (i : N.Inputs) :
  R.v27290 (state s) (inputs i) = Zmod.unsigned (N.v27290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27290 s i)) at 1.
  unfold R.v27290, N.v27290.
  rewrite ?node_27285.
  rewrite ?node_27289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27291 (s : N.State) (i : N.Inputs) :
  R.v27291 (state s) (inputs i) = Zmod.unsigned (N.v27291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27291 s i)) at 1.
  unfold R.v27291, N.v27291.
  unfold R.v6, N.v6.
  rewrite ?node_27290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27292 (s : N.State) (i : N.Inputs) :
  R.v27292 (state s) (inputs i) = Zmod.unsigned (N.v27292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27292 s i)) at 1.
  unfold R.v27292, N.v27292.
  rewrite ?node_10482.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27293 (s : N.State) (i : N.Inputs) :
  R.v27293 (state s) (inputs i) = Zmod.unsigned (N.v27293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27293 s i)) at 1.
  unfold R.v27293, N.v27293.
  unfold R.v6, N.v6.
  rewrite ?node_10646.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27294 (s : N.State) (i : N.Inputs) :
  R.v27294 (state s) (inputs i) = Zmod.unsigned (N.v27294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27294 s i)) at 1.
  unfold R.v27294, N.v27294.
  rewrite ?node_27292.
  rewrite ?node_27293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27295 (s : N.State) (i : N.Inputs) :
  R.v27295 (state s) (inputs i) = Zmod.unsigned (N.v27295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27295 s i)) at 1.
  unfold R.v27295, N.v27295.
  rewrite ?node_27291.
  rewrite ?node_27294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27296 (s : N.State) (i : N.Inputs) :
  R.v27296 (state s) (inputs i) = Zmod.unsigned (N.v27296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27296 s i)) at 1.
  unfold R.v27296, N.v27296.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27297 (s : N.State) (i : N.Inputs) :
  R.v27297 (state s) (inputs i) = Zmod.unsigned (N.v27297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27297 s i)) at 1.
  unfold R.v27297, N.v27297.
  rewrite ?node_10486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27298 (s : N.State) (i : N.Inputs) :
  R.v27298 (state s) (inputs i) = Zmod.unsigned (N.v27298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27298 s i)) at 1.
  unfold R.v27298, N.v27298.
  unfold R.v6, N.v6.
  rewrite !state_r1177_nr_5F1177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1177_nr_5F1177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27299 (s : N.State) (i : N.Inputs) :
  R.v27299 (state s) (inputs i) = Zmod.unsigned (N.v27299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27299 s i)) at 1.
  unfold R.v27299, N.v27299.
  unfold R.v6, N.v6.
  rewrite ?node_10482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27300 (s : N.State) (i : N.Inputs) :
  R.v27300 (state s) (inputs i) = Zmod.unsigned (N.v27300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27300 s i)) at 1.
  unfold R.v27300, N.v27300.
  rewrite ?node_27298.
  rewrite ?node_27299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27301 (s : N.State) (i : N.Inputs) :
  R.v27301 (state s) (inputs i) = Zmod.unsigned (N.v27301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27301 s i)) at 1.
  unfold R.v27301, N.v27301.
  unfold R.v16484, N.v16484.
  rewrite ?node_27300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27302 (s : N.State) (i : N.Inputs) :
  R.v27302 (state s) (inputs i) = Zmod.unsigned (N.v27302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27302 s i)) at 1.
  unfold R.v27302, N.v27302.
  rewrite ?node_27297.
  rewrite ?node_27301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27303 (s : N.State) (i : N.Inputs) :
  R.v27303 (state s) (inputs i) = Zmod.unsigned (N.v27303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27303 s i)) at 1.
  unfold R.v27303, N.v27303.
  unfold R.v6, N.v6.
  rewrite ?node_27302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27304 (s : N.State) (i : N.Inputs) :
  R.v27304 (state s) (inputs i) = Zmod.unsigned (N.v27304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27304 s i)) at 1.
  unfold R.v27304, N.v27304.
  rewrite ?node_10487.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27305 (s : N.State) (i : N.Inputs) :
  R.v27305 (state s) (inputs i) = Zmod.unsigned (N.v27305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27305 s i)) at 1.
  unfold R.v27305, N.v27305.
  unfold R.v6, N.v6.
  rewrite ?node_10696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27306 (s : N.State) (i : N.Inputs) :
  R.v27306 (state s) (inputs i) = Zmod.unsigned (N.v27306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27306 s i)) at 1.
  unfold R.v27306, N.v27306.
  rewrite ?node_27304.
  rewrite ?node_27305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27307 (s : N.State) (i : N.Inputs) :
  R.v27307 (state s) (inputs i) = Zmod.unsigned (N.v27307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27307 s i)) at 1.
  unfold R.v27307, N.v27307.
  rewrite ?node_27303.
  rewrite ?node_27306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27308 (s : N.State) (i : N.Inputs) :
  R.v27308 (state s) (inputs i) = Zmod.unsigned (N.v27308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27308 s i)) at 1.
  unfold R.v27308, N.v27308.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27309 (s : N.State) (i : N.Inputs) :
  R.v27309 (state s) (inputs i) = Zmod.unsigned (N.v27309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27309 s i)) at 1.
  unfold R.v27309, N.v27309.
  rewrite ?node_10494.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27310 (s : N.State) (i : N.Inputs) :
  R.v27310 (state s) (inputs i) = Zmod.unsigned (N.v27310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27310 s i)) at 1.
  unfold R.v27310, N.v27310.
  unfold R.v16463, N.v16463.
  rewrite !state_r1181_nr_5F1181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1181_nr_5F1181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27311 (s : N.State) (i : N.Inputs) :
  R.v27311 (state s) (inputs i) = Zmod.unsigned (N.v27311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27311 s i)) at 1.
  unfold R.v27311, N.v27311.
  unfold R.v16463, N.v16463.
  rewrite !state_r1180_nr_5F1180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1180_nr_5F1180 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27312 (s : N.State) (i : N.Inputs) :
  R.v27312 (state s) (inputs i) = Zmod.unsigned (N.v27312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27312 s i)) at 1.
  unfold R.v27312, N.v27312.
  unfold R.v6, N.v6.
  rewrite !state_r1179_nr_5F1179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1179_nr_5F1179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27313 (s : N.State) (i : N.Inputs) :
  R.v27313 (state s) (inputs i) = Zmod.unsigned (N.v27313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27313 s i)) at 1.
  unfold R.v27313, N.v27313.
  unfold R.v6, N.v6.
  rewrite !state_r1178_nr_5F1178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1178_nr_5F1178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27314 (s : N.State) (i : N.Inputs) :
  R.v27314 (state s) (inputs i) = Zmod.unsigned (N.v27314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27314 s i)) at 1.
  unfold R.v27314, N.v27314.
  rewrite ?node_27312.
  rewrite ?node_27313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27315 (s : N.State) (i : N.Inputs) :
  R.v27315 (state s) (inputs i) = Zmod.unsigned (N.v27315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27315 s i)) at 1.
  unfold R.v27315, N.v27315.
  unfold R.v16484, N.v16484.
  rewrite ?node_27314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27316 (s : N.State) (i : N.Inputs) :
  R.v27316 (state s) (inputs i) = Zmod.unsigned (N.v27316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27316 s i)) at 1.
  unfold R.v27316, N.v27316.
  rewrite ?node_27309.
  rewrite ?node_27310.
  rewrite ?node_27311.
  rewrite ?node_27315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27317 (s : N.State) (i : N.Inputs) :
  R.v27317 (state s) (inputs i) = Zmod.unsigned (N.v27317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27317 s i)) at 1.
  unfold R.v27317, N.v27317.
  unfold R.v6, N.v6.
  rewrite ?node_27316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27318 (s : N.State) (i : N.Inputs) :
  R.v27318 (state s) (inputs i) = Zmod.unsigned (N.v27318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27318 s i)) at 1.
  unfold R.v27318, N.v27318.
  rewrite ?node_10495.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27319 (s : N.State) (i : N.Inputs) :
  R.v27319 (state s) (inputs i) = Zmod.unsigned (N.v27319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27319 s i)) at 1.
  unfold R.v27319, N.v27319.
  unfold R.v6, N.v6.
  rewrite ?node_10654.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27320 (s : N.State) (i : N.Inputs) :
  R.v27320 (state s) (inputs i) = Zmod.unsigned (N.v27320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27320 s i)) at 1.
  unfold R.v27320, N.v27320.
  unfold R.v6, N.v6.
  rewrite ?node_10700.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27321 (s : N.State) (i : N.Inputs) :
  R.v27321 (state s) (inputs i) = Zmod.unsigned (N.v27321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27321 s i)) at 1.
  unfold R.v27321, N.v27321.
  rewrite ?node_27318.
  rewrite ?node_27319.
  rewrite ?node_27320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27322 (s : N.State) (i : N.Inputs) :
  R.v27322 (state s) (inputs i) = Zmod.unsigned (N.v27322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27322 s i)) at 1.
  unfold R.v27322, N.v27322.
  rewrite ?node_27317.
  rewrite ?node_27321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27323 (s : N.State) (i : N.Inputs) :
  R.v27323 (state s) (inputs i) = Zmod.unsigned (N.v27323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27323 s i)) at 1.
  unfold R.v27323, N.v27323.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27324 (s : N.State) (i : N.Inputs) :
  R.v27324 (state s) (inputs i) = Zmod.unsigned (N.v27324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27324 s i)) at 1.
  unfold R.v27324, N.v27324.
  unfold R.v16463, N.v16463.
  rewrite !state_r1180_nr_5F1180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1180_nr_5F1180 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27325 (s : N.State) (i : N.Inputs) :
  R.v27325 (state s) (inputs i) = Zmod.unsigned (N.v27325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27325 s i)) at 1.
  unfold R.v27325, N.v27325.
  unfold R.v6, N.v6.
  rewrite !state_r1179_nr_5F1179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1179_nr_5F1179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27326 (s : N.State) (i : N.Inputs) :
  R.v27326 (state s) (inputs i) = Zmod.unsigned (N.v27326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27326 s i)) at 1.
  unfold R.v27326, N.v27326.
  unfold R.v6, N.v6.
  rewrite !state_r1178_nr_5F1178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1178_nr_5F1178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27327 (s : N.State) (i : N.Inputs) :
  R.v27327 (state s) (inputs i) = Zmod.unsigned (N.v27327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27327 s i)) at 1.
  unfold R.v27327, N.v27327.
  rewrite ?node_27325.
  rewrite ?node_27326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27328 (s : N.State) (i : N.Inputs) :
  R.v27328 (state s) (inputs i) = Zmod.unsigned (N.v27328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27328 s i)) at 1.
  unfold R.v27328, N.v27328.
  unfold R.v16484, N.v16484.
  rewrite ?node_27327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27329 (s : N.State) (i : N.Inputs) :
  R.v27329 (state s) (inputs i) = Zmod.unsigned (N.v27329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27329 s i)) at 1.
  unfold R.v27329, N.v27329.
  rewrite ?node_27324.
  rewrite ?node_27328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27330 (s : N.State) (i : N.Inputs) :
  R.v27330 (state s) (inputs i) = Zmod.unsigned (N.v27330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27330 s i)) at 1.
  unfold R.v27330, N.v27330.
  unfold R.v6, N.v6.
  rewrite ?node_27329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27331 (s : N.State) (i : N.Inputs) :
  R.v27331 (state s) (inputs i) = Zmod.unsigned (N.v27331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27331 s i)) at 1.
  unfold R.v27331, N.v27331.
  rewrite ?node_10490.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27332 (s : N.State) (i : N.Inputs) :
  R.v27332 (state s) (inputs i) = Zmod.unsigned (N.v27332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27332 s i)) at 1.
  unfold R.v27332, N.v27332.
  unfold R.v6, N.v6.
  rewrite ?node_10654.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27333 (s : N.State) (i : N.Inputs) :
  R.v27333 (state s) (inputs i) = Zmod.unsigned (N.v27333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27333 s i)) at 1.
  unfold R.v27333, N.v27333.
  rewrite ?node_27331.
  rewrite ?node_27332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27334 (s : N.State) (i : N.Inputs) :
  R.v27334 (state s) (inputs i) = Zmod.unsigned (N.v27334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27334 s i)) at 1.
  unfold R.v27334, N.v27334.
  rewrite ?node_27330.
  rewrite ?node_27333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27335 (s : N.State) (i : N.Inputs) :
  R.v27335 (state s) (inputs i) = Zmod.unsigned (N.v27335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27335 s i)) at 1.
  unfold R.v27335, N.v27335.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27336 (s : N.State) (i : N.Inputs) :
  R.v27336 (state s) (inputs i) = Zmod.unsigned (N.v27336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27336 s i)) at 1.
  unfold R.v27336, N.v27336.
  rewrite ?node_10494.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27337 (s : N.State) (i : N.Inputs) :
  R.v27337 (state s) (inputs i) = Zmod.unsigned (N.v27337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27337 s i)) at 1.
  unfold R.v27337, N.v27337.
  unfold R.v6, N.v6.
  rewrite !state_r1181_nr_5F1181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1181_nr_5F1181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27338 (s : N.State) (i : N.Inputs) :
  R.v27338 (state s) (inputs i) = Zmod.unsigned (N.v27338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27338 s i)) at 1.
  unfold R.v27338, N.v27338.
  unfold R.v6, N.v6.
  rewrite ?node_10490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27339 (s : N.State) (i : N.Inputs) :
  R.v27339 (state s) (inputs i) = Zmod.unsigned (N.v27339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27339 s i)) at 1.
  unfold R.v27339, N.v27339.
  rewrite ?node_27337.
  rewrite ?node_27338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27340 (s : N.State) (i : N.Inputs) :
  R.v27340 (state s) (inputs i) = Zmod.unsigned (N.v27340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27340 s i)) at 1.
  unfold R.v27340, N.v27340.
  unfold R.v16484, N.v16484.
  rewrite ?node_27339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27341 (s : N.State) (i : N.Inputs) :
  R.v27341 (state s) (inputs i) = Zmod.unsigned (N.v27341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27341 s i)) at 1.
  unfold R.v27341, N.v27341.
  rewrite ?node_27336.
  rewrite ?node_27340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27342 (s : N.State) (i : N.Inputs) :
  R.v27342 (state s) (inputs i) = Zmod.unsigned (N.v27342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27342 s i)) at 1.
  unfold R.v27342, N.v27342.
  unfold R.v6, N.v6.
  rewrite ?node_27341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27343 (s : N.State) (i : N.Inputs) :
  R.v27343 (state s) (inputs i) = Zmod.unsigned (N.v27343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27343 s i)) at 1.
  unfold R.v27343, N.v27343.
  rewrite ?node_10495.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27344 (s : N.State) (i : N.Inputs) :
  R.v27344 (state s) (inputs i) = Zmod.unsigned (N.v27344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27344 s i)) at 1.
  unfold R.v27344, N.v27344.
  unfold R.v6, N.v6.
  rewrite ?node_10700.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27345 (s : N.State) (i : N.Inputs) :
  R.v27345 (state s) (inputs i) = Zmod.unsigned (N.v27345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27345 s i)) at 1.
  unfold R.v27345, N.v27345.
  rewrite ?node_27343.
  rewrite ?node_27344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27346 (s : N.State) (i : N.Inputs) :
  R.v27346 (state s) (inputs i) = Zmod.unsigned (N.v27346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27346 s i)) at 1.
  unfold R.v27346, N.v27346.
  rewrite ?node_27342.
  rewrite ?node_27345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27347 (s : N.State) (i : N.Inputs) :
  R.v27347 (state s) (inputs i) = Zmod.unsigned (N.v27347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27347 s i)) at 1.
  unfold R.v27347, N.v27347.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27348 (s : N.State) (i : N.Inputs) :
  R.v27348 (state s) (inputs i) = Zmod.unsigned (N.v27348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27348 s i)) at 1.
  unfold R.v27348, N.v27348.
  rewrite ?node_10502.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27349 (s : N.State) (i : N.Inputs) :
  R.v27349 (state s) (inputs i) = Zmod.unsigned (N.v27349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27349 s i)) at 1.
  unfold R.v27349, N.v27349.
  unfold R.v16463, N.v16463.
  rewrite !state_r1185_nr_5F1185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1185_nr_5F1185 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27350 (s : N.State) (i : N.Inputs) :
  R.v27350 (state s) (inputs i) = Zmod.unsigned (N.v27350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27350 s i)) at 1.
  unfold R.v27350, N.v27350.
  unfold R.v16463, N.v16463.
  rewrite !state_r1184_nr_5F1184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1184_nr_5F1184 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27351 (s : N.State) (i : N.Inputs) :
  R.v27351 (state s) (inputs i) = Zmod.unsigned (N.v27351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27351 s i)) at 1.
  unfold R.v27351, N.v27351.
  unfold R.v6, N.v6.
  rewrite !state_r1183_nr_5F1183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1183_nr_5F1183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27352 (s : N.State) (i : N.Inputs) :
  R.v27352 (state s) (inputs i) = Zmod.unsigned (N.v27352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27352 s i)) at 1.
  unfold R.v27352, N.v27352.
  unfold R.v6, N.v6.
  rewrite !state_r1182_nr_5F1182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1182_nr_5F1182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27353 (s : N.State) (i : N.Inputs) :
  R.v27353 (state s) (inputs i) = Zmod.unsigned (N.v27353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27353 s i)) at 1.
  unfold R.v27353, N.v27353.
  rewrite ?node_27351.
  rewrite ?node_27352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27354 (s : N.State) (i : N.Inputs) :
  R.v27354 (state s) (inputs i) = Zmod.unsigned (N.v27354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27354 s i)) at 1.
  unfold R.v27354, N.v27354.
  unfold R.v16484, N.v16484.
  rewrite ?node_27353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27355 (s : N.State) (i : N.Inputs) :
  R.v27355 (state s) (inputs i) = Zmod.unsigned (N.v27355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27355 s i)) at 1.
  unfold R.v27355, N.v27355.
  rewrite ?node_27348.
  rewrite ?node_27349.
  rewrite ?node_27350.
  rewrite ?node_27354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27356 (s : N.State) (i : N.Inputs) :
  R.v27356 (state s) (inputs i) = Zmod.unsigned (N.v27356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27356 s i)) at 1.
  unfold R.v27356, N.v27356.
  unfold R.v6, N.v6.
  rewrite ?node_27355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27357 (s : N.State) (i : N.Inputs) :
  R.v27357 (state s) (inputs i) = Zmod.unsigned (N.v27357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27357 s i)) at 1.
  unfold R.v27357, N.v27357.
  rewrite ?node_10503.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27358 (s : N.State) (i : N.Inputs) :
  R.v27358 (state s) (inputs i) = Zmod.unsigned (N.v27358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27358 s i)) at 1.
  unfold R.v27358, N.v27358.
  unfold R.v6, N.v6.
  rewrite ?node_10662.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27359 (s : N.State) (i : N.Inputs) :
  R.v27359 (state s) (inputs i) = Zmod.unsigned (N.v27359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27359 s i)) at 1.
  unfold R.v27359, N.v27359.
  unfold R.v6, N.v6.
  rewrite ?node_10713.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27360 (s : N.State) (i : N.Inputs) :
  R.v27360 (state s) (inputs i) = Zmod.unsigned (N.v27360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27360 s i)) at 1.
  unfold R.v27360, N.v27360.
  rewrite ?node_27357.
  rewrite ?node_27358.
  rewrite ?node_27359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27361 (s : N.State) (i : N.Inputs) :
  R.v27361 (state s) (inputs i) = Zmod.unsigned (N.v27361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27361 s i)) at 1.
  unfold R.v27361, N.v27361.
  rewrite ?node_27356.
  rewrite ?node_27360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27362 (s : N.State) (i : N.Inputs) :
  R.v27362 (state s) (inputs i) = Zmod.unsigned (N.v27362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27362 s i)) at 1.
  unfold R.v27362, N.v27362.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27363 (s : N.State) (i : N.Inputs) :
  R.v27363 (state s) (inputs i) = Zmod.unsigned (N.v27363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27363 s i)) at 1.
  unfold R.v27363, N.v27363.
  unfold R.v16463, N.v16463.
  rewrite !state_r1184_nr_5F1184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1184_nr_5F1184 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27364 (s : N.State) (i : N.Inputs) :
  R.v27364 (state s) (inputs i) = Zmod.unsigned (N.v27364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27364 s i)) at 1.
  unfold R.v27364, N.v27364.
  unfold R.v6, N.v6.
  rewrite !state_r1183_nr_5F1183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1183_nr_5F1183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27365 (s : N.State) (i : N.Inputs) :
  R.v27365 (state s) (inputs i) = Zmod.unsigned (N.v27365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27365 s i)) at 1.
  unfold R.v27365, N.v27365.
  unfold R.v6, N.v6.
  rewrite !state_r1182_nr_5F1182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1182_nr_5F1182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27366 (s : N.State) (i : N.Inputs) :
  R.v27366 (state s) (inputs i) = Zmod.unsigned (N.v27366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27366 s i)) at 1.
  unfold R.v27366, N.v27366.
  rewrite ?node_27364.
  rewrite ?node_27365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27367 (s : N.State) (i : N.Inputs) :
  R.v27367 (state s) (inputs i) = Zmod.unsigned (N.v27367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27367 s i)) at 1.
  unfold R.v27367, N.v27367.
  unfold R.v16484, N.v16484.
  rewrite ?node_27366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27368 (s : N.State) (i : N.Inputs) :
  R.v27368 (state s) (inputs i) = Zmod.unsigned (N.v27368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27368 s i)) at 1.
  unfold R.v27368, N.v27368.
  rewrite ?node_27363.
  rewrite ?node_27367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27369 (s : N.State) (i : N.Inputs) :
  R.v27369 (state s) (inputs i) = Zmod.unsigned (N.v27369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27369 s i)) at 1.
  unfold R.v27369, N.v27369.
  unfold R.v6, N.v6.
  rewrite ?node_27368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27370 (s : N.State) (i : N.Inputs) :
  R.v27370 (state s) (inputs i) = Zmod.unsigned (N.v27370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27370 s i)) at 1.
  unfold R.v27370, N.v27370.
  rewrite ?node_10498.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27371 (s : N.State) (i : N.Inputs) :
  R.v27371 (state s) (inputs i) = Zmod.unsigned (N.v27371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27371 s i)) at 1.
  unfold R.v27371, N.v27371.
  unfold R.v6, N.v6.
  rewrite ?node_10662.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27372 (s : N.State) (i : N.Inputs) :
  R.v27372 (state s) (inputs i) = Zmod.unsigned (N.v27372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27372 s i)) at 1.
  unfold R.v27372, N.v27372.
  rewrite ?node_27370.
  rewrite ?node_27371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27373 (s : N.State) (i : N.Inputs) :
  R.v27373 (state s) (inputs i) = Zmod.unsigned (N.v27373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27373 s i)) at 1.
  unfold R.v27373, N.v27373.
  rewrite ?node_27369.
  rewrite ?node_27372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27374 (s : N.State) (i : N.Inputs) :
  R.v27374 (state s) (inputs i) = Zmod.unsigned (N.v27374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27374 s i)) at 1.
  unfold R.v27374, N.v27374.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27375 (s : N.State) (i : N.Inputs) :
  R.v27375 (state s) (inputs i) = Zmod.unsigned (N.v27375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27375 s i)) at 1.
  unfold R.v27375, N.v27375.
  rewrite ?node_10502.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27376 (s : N.State) (i : N.Inputs) :
  R.v27376 (state s) (inputs i) = Zmod.unsigned (N.v27376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27376 s i)) at 1.
  unfold R.v27376, N.v27376.
  unfold R.v6, N.v6.
  rewrite !state_r1185_nr_5F1185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1185_nr_5F1185 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27377 (s : N.State) (i : N.Inputs) :
  R.v27377 (state s) (inputs i) = Zmod.unsigned (N.v27377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27377 s i)) at 1.
  unfold R.v27377, N.v27377.
  unfold R.v6, N.v6.
  rewrite ?node_10498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27378 (s : N.State) (i : N.Inputs) :
  R.v27378 (state s) (inputs i) = Zmod.unsigned (N.v27378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27378 s i)) at 1.
  unfold R.v27378, N.v27378.
  rewrite ?node_27376.
  rewrite ?node_27377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27379 (s : N.State) (i : N.Inputs) :
  R.v27379 (state s) (inputs i) = Zmod.unsigned (N.v27379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27379 s i)) at 1.
  unfold R.v27379, N.v27379.
  unfold R.v16484, N.v16484.
  rewrite ?node_27378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27380 (s : N.State) (i : N.Inputs) :
  R.v27380 (state s) (inputs i) = Zmod.unsigned (N.v27380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27380 s i)) at 1.
  unfold R.v27380, N.v27380.
  rewrite ?node_27375.
  rewrite ?node_27379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27381 (s : N.State) (i : N.Inputs) :
  R.v27381 (state s) (inputs i) = Zmod.unsigned (N.v27381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27381 s i)) at 1.
  unfold R.v27381, N.v27381.
  unfold R.v6, N.v6.
  rewrite ?node_27380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27382 (s : N.State) (i : N.Inputs) :
  R.v27382 (state s) (inputs i) = Zmod.unsigned (N.v27382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27382 s i)) at 1.
  unfold R.v27382, N.v27382.
  rewrite ?node_10503.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27383 (s : N.State) (i : N.Inputs) :
  R.v27383 (state s) (inputs i) = Zmod.unsigned (N.v27383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27383 s i)) at 1.
  unfold R.v27383, N.v27383.
  unfold R.v6, N.v6.
  rewrite ?node_10713.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27384 (s : N.State) (i : N.Inputs) :
  R.v27384 (state s) (inputs i) = Zmod.unsigned (N.v27384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27384 s i)) at 1.
  unfold R.v27384, N.v27384.
  rewrite ?node_27382.
  rewrite ?node_27383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27385 (s : N.State) (i : N.Inputs) :
  R.v27385 (state s) (inputs i) = Zmod.unsigned (N.v27385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27385 s i)) at 1.
  unfold R.v27385, N.v27385.
  rewrite ?node_27381.
  rewrite ?node_27384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27386 (s : N.State) (i : N.Inputs) :
  R.v27386 (state s) (inputs i) = Zmod.unsigned (N.v27386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27386 s i)) at 1.
  unfold R.v27386, N.v27386.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27387 (s : N.State) (i : N.Inputs) :
  R.v27387 (state s) (inputs i) = Zmod.unsigned (N.v27387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27387 s i)) at 1.
  unfold R.v27387, N.v27387.
  unfold R.v6, N.v6.
  rewrite !state_r1187_nr_5F1187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1187_nr_5F1187 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27388 (s : N.State) (i : N.Inputs) :
  R.v27388 (state s) (inputs i) = Zmod.unsigned (N.v27388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27388 s i)) at 1.
  unfold R.v27388, N.v27388.
  unfold R.v6, N.v6.
  rewrite !state_r1186_nr_5F1186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1186_nr_5F1186 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27389 (s : N.State) (i : N.Inputs) :
  R.v27389 (state s) (inputs i) = Zmod.unsigned (N.v27389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27389 s i)) at 1.
  unfold R.v27389, N.v27389.
  rewrite ?node_27387.
  rewrite ?node_27388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27390 (s : N.State) (i : N.Inputs) :
  R.v27390 (state s) (inputs i) = Zmod.unsigned (N.v27390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27390 s i)) at 1.
  unfold R.v27390, N.v27390.
  unfold R.v16463, N.v16463.
  rewrite ?node_27389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27391 (s : N.State) (i : N.Inputs) :
  R.v27391 (state s) (inputs i) = Zmod.unsigned (N.v27391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27391 s i)) at 1.
  unfold R.v27391, N.v27391.
  rewrite ?node_10510.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27392 (s : N.State) (i : N.Inputs) :
  R.v27392 (state s) (inputs i) = Zmod.unsigned (N.v27392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27392 s i)) at 1.
  unfold R.v27392, N.v27392.
  unfold R.v6, N.v6.
  rewrite ?node_10714.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27393 (s : N.State) (i : N.Inputs) :
  R.v27393 (state s) (inputs i) = Zmod.unsigned (N.v27393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27393 s i)) at 1.
  unfold R.v27393, N.v27393.
  rewrite ?node_27391.
  rewrite ?node_27392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27394 (s : N.State) (i : N.Inputs) :
  R.v27394 (state s) (inputs i) = Zmod.unsigned (N.v27394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27394 s i)) at 1.
  unfold R.v27394, N.v27394.
  rewrite ?node_27390.
  rewrite ?node_27393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27395 (s : N.State) (i : N.Inputs) :
  R.v27395 (state s) (inputs i) = Zmod.unsigned (N.v27395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27395 s i)) at 1.
  unfold R.v27395, N.v27395.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27396 (s : N.State) (i : N.Inputs) :
  R.v27396 (state s) (inputs i) = Zmod.unsigned (N.v27396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27396 s i)) at 1.
  unfold R.v27396, N.v27396.
  rewrite ?node_10604.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27397 (s : N.State) (i : N.Inputs) :
  R.v27397 (state s) (inputs i) = Zmod.unsigned (N.v27397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27397 s i)) at 1.
  unfold R.v27397, N.v27397.
  unfold R.v16463, N.v16463.
  rewrite !state_r1191_nr_5F1191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1191_nr_5F1191 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27398 (s : N.State) (i : N.Inputs) :
  R.v27398 (state s) (inputs i) = Zmod.unsigned (N.v27398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27398 s i)) at 1.
  unfold R.v27398, N.v27398.
  unfold R.v16463, N.v16463.
  rewrite !state_r1190_nr_5F1190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1190_nr_5F1190 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27399 (s : N.State) (i : N.Inputs) :
  R.v27399 (state s) (inputs i) = Zmod.unsigned (N.v27399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27399 s i)) at 1.
  unfold R.v27399, N.v27399.
  unfold R.v6, N.v6.
  rewrite !state_r1189_nr_5F1189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1189_nr_5F1189 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27400 (s : N.State) (i : N.Inputs) :
  R.v27400 (state s) (inputs i) = Zmod.unsigned (N.v27400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27400 s i)) at 1.
  unfold R.v27400, N.v27400.
  unfold R.v6, N.v6.
  rewrite !state_r1188_nr_5F1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1188_nr_5F1188 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27401 (s : N.State) (i : N.Inputs) :
  R.v27401 (state s) (inputs i) = Zmod.unsigned (N.v27401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27401 s i)) at 1.
  unfold R.v27401, N.v27401.
  rewrite ?node_27399.
  rewrite ?node_27400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27402 (s : N.State) (i : N.Inputs) :
  R.v27402 (state s) (inputs i) = Zmod.unsigned (N.v27402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27402 s i)) at 1.
  unfold R.v27402, N.v27402.
  unfold R.v16484, N.v16484.
  rewrite ?node_27401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27403 (s : N.State) (i : N.Inputs) :
  R.v27403 (state s) (inputs i) = Zmod.unsigned (N.v27403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27403 s i)) at 1.
  unfold R.v27403, N.v27403.
  rewrite ?node_27396.
  rewrite ?node_27397.
  rewrite ?node_27398.
  rewrite ?node_27402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27404 (s : N.State) (i : N.Inputs) :
  R.v27404 (state s) (inputs i) = Zmod.unsigned (N.v27404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27404 s i)) at 1.
  unfold R.v27404, N.v27404.
  unfold R.v6, N.v6.
  rewrite ?node_27403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27405 (s : N.State) (i : N.Inputs) :
  R.v27405 (state s) (inputs i) = Zmod.unsigned (N.v27405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27405 s i)) at 1.
  unfold R.v27405, N.v27405.
  rewrite ?node_10605.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27406 (s : N.State) (i : N.Inputs) :
  R.v27406 (state s) (inputs i) = Zmod.unsigned (N.v27406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27406 s i)) at 1.
  unfold R.v27406, N.v27406.
  unfold R.v6, N.v6.
  rewrite ?node_10765.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27407 (s : N.State) (i : N.Inputs) :
  R.v27407 (state s) (inputs i) = Zmod.unsigned (N.v27407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27407 s i)) at 1.
  unfold R.v27407, N.v27407.
  unfold R.v6, N.v6.
  rewrite ?node_10833.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27408 (s : N.State) (i : N.Inputs) :
  R.v27408 (state s) (inputs i) = Zmod.unsigned (N.v27408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27408 s i)) at 1.
  unfold R.v27408, N.v27408.
  rewrite ?node_27405.
  rewrite ?node_27406.
  rewrite ?node_27407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27409 (s : N.State) (i : N.Inputs) :
  R.v27409 (state s) (inputs i) = Zmod.unsigned (N.v27409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27409 s i)) at 1.
  unfold R.v27409, N.v27409.
  rewrite ?node_27404.
  rewrite ?node_27408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27410 (s : N.State) (i : N.Inputs) :
  R.v27410 (state s) (inputs i) = Zmod.unsigned (N.v27410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27410 s i)) at 1.
  unfold R.v27410, N.v27410.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27411 (s : N.State) (i : N.Inputs) :
  R.v27411 (state s) (inputs i) = Zmod.unsigned (N.v27411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27411 s i)) at 1.
  unfold R.v27411, N.v27411.
  unfold R.v16463, N.v16463.
  rewrite !state_r1190_nr_5F1190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1190_nr_5F1190 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27412 (s : N.State) (i : N.Inputs) :
  R.v27412 (state s) (inputs i) = Zmod.unsigned (N.v27412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27412 s i)) at 1.
  unfold R.v27412, N.v27412.
  unfold R.v6, N.v6.
  rewrite !state_r1189_nr_5F1189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1189_nr_5F1189 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27413 (s : N.State) (i : N.Inputs) :
  R.v27413 (state s) (inputs i) = Zmod.unsigned (N.v27413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27413 s i)) at 1.
  unfold R.v27413, N.v27413.
  unfold R.v6, N.v6.
  rewrite !state_r1188_nr_5F1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1188_nr_5F1188 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27414 (s : N.State) (i : N.Inputs) :
  R.v27414 (state s) (inputs i) = Zmod.unsigned (N.v27414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27414 s i)) at 1.
  unfold R.v27414, N.v27414.
  rewrite ?node_27412.
  rewrite ?node_27413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27415 (s : N.State) (i : N.Inputs) :
  R.v27415 (state s) (inputs i) = Zmod.unsigned (N.v27415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27415 s i)) at 1.
  unfold R.v27415, N.v27415.
  unfold R.v16484, N.v16484.
  rewrite ?node_27414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27416 (s : N.State) (i : N.Inputs) :
  R.v27416 (state s) (inputs i) = Zmod.unsigned (N.v27416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27416 s i)) at 1.
  unfold R.v27416, N.v27416.
  rewrite ?node_27411.
  rewrite ?node_27415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27417 (s : N.State) (i : N.Inputs) :
  R.v27417 (state s) (inputs i) = Zmod.unsigned (N.v27417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27417 s i)) at 1.
  unfold R.v27417, N.v27417.
  unfold R.v6, N.v6.
  rewrite ?node_27416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27418 (s : N.State) (i : N.Inputs) :
  R.v27418 (state s) (inputs i) = Zmod.unsigned (N.v27418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27418 s i)) at 1.
  unfold R.v27418, N.v27418.
  rewrite ?node_10600.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27419 (s : N.State) (i : N.Inputs) :
  R.v27419 (state s) (inputs i) = Zmod.unsigned (N.v27419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27419 s i)) at 1.
  unfold R.v27419, N.v27419.
  unfold R.v6, N.v6.
  rewrite ?node_10765.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27420 (s : N.State) (i : N.Inputs) :
  R.v27420 (state s) (inputs i) = Zmod.unsigned (N.v27420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27420 s i)) at 1.
  unfold R.v27420, N.v27420.
  rewrite ?node_27418.
  rewrite ?node_27419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27421 (s : N.State) (i : N.Inputs) :
  R.v27421 (state s) (inputs i) = Zmod.unsigned (N.v27421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27421 s i)) at 1.
  unfold R.v27421, N.v27421.
  rewrite ?node_27417.
  rewrite ?node_27420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27422 (s : N.State) (i : N.Inputs) :
  R.v27422 (state s) (inputs i) = Zmod.unsigned (N.v27422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27422 s i)) at 1.
  unfold R.v27422, N.v27422.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27423 (s : N.State) (i : N.Inputs) :
  R.v27423 (state s) (inputs i) = Zmod.unsigned (N.v27423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27423 s i)) at 1.
  unfold R.v27423, N.v27423.
  rewrite ?node_10604.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27424 (s : N.State) (i : N.Inputs) :
  R.v27424 (state s) (inputs i) = Zmod.unsigned (N.v27424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27424 s i)) at 1.
  unfold R.v27424, N.v27424.
  unfold R.v6, N.v6.
  rewrite !state_r1191_nr_5F1191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1191_nr_5F1191 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27425 (s : N.State) (i : N.Inputs) :
  R.v27425 (state s) (inputs i) = Zmod.unsigned (N.v27425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27425 s i)) at 1.
  unfold R.v27425, N.v27425.
  unfold R.v6, N.v6.
  rewrite ?node_10600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27426 (s : N.State) (i : N.Inputs) :
  R.v27426 (state s) (inputs i) = Zmod.unsigned (N.v27426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27426 s i)) at 1.
  unfold R.v27426, N.v27426.
  rewrite ?node_27424.
  rewrite ?node_27425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27427 (s : N.State) (i : N.Inputs) :
  R.v27427 (state s) (inputs i) = Zmod.unsigned (N.v27427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27427 s i)) at 1.
  unfold R.v27427, N.v27427.
  unfold R.v16484, N.v16484.
  rewrite ?node_27426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27428 (s : N.State) (i : N.Inputs) :
  R.v27428 (state s) (inputs i) = Zmod.unsigned (N.v27428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27428 s i)) at 1.
  unfold R.v27428, N.v27428.
  rewrite ?node_27423.
  rewrite ?node_27427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27429 (s : N.State) (i : N.Inputs) :
  R.v27429 (state s) (inputs i) = Zmod.unsigned (N.v27429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27429 s i)) at 1.
  unfold R.v27429, N.v27429.
  unfold R.v6, N.v6.
  rewrite ?node_27428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27430 (s : N.State) (i : N.Inputs) :
  R.v27430 (state s) (inputs i) = Zmod.unsigned (N.v27430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27430 s i)) at 1.
  unfold R.v27430, N.v27430.
  rewrite ?node_10605.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27431 (s : N.State) (i : N.Inputs) :
  R.v27431 (state s) (inputs i) = Zmod.unsigned (N.v27431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27431 s i)) at 1.
  unfold R.v27431, N.v27431.
  unfold R.v6, N.v6.
  rewrite ?node_10833.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27432 (s : N.State) (i : N.Inputs) :
  R.v27432 (state s) (inputs i) = Zmod.unsigned (N.v27432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27432 s i)) at 1.
  unfold R.v27432, N.v27432.
  rewrite ?node_27430.
  rewrite ?node_27431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27433 (s : N.State) (i : N.Inputs) :
  R.v27433 (state s) (inputs i) = Zmod.unsigned (N.v27433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27433 s i)) at 1.
  unfold R.v27433, N.v27433.
  rewrite ?node_27429.
  rewrite ?node_27432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27434 (s : N.State) (i : N.Inputs) :
  R.v27434 (state s) (inputs i) = Zmod.unsigned (N.v27434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27434 s i)) at 1.
  unfold R.v27434, N.v27434.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27435 (s : N.State) (i : N.Inputs) :
  R.v27435 (state s) (inputs i) = Zmod.unsigned (N.v27435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27435 s i)) at 1.
  unfold R.v27435, N.v27435.
  rewrite ?node_10611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27436 (s : N.State) (i : N.Inputs) :
  R.v27436 (state s) (inputs i) = Zmod.unsigned (N.v27436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27436 s i)) at 1.
  unfold R.v27436, N.v27436.
  unfold R.v16463, N.v16463.
  rewrite !state_r1195_nr_5F1195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1195_nr_5F1195 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27437 (s : N.State) (i : N.Inputs) :
  R.v27437 (state s) (inputs i) = Zmod.unsigned (N.v27437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27437 s i)) at 1.
  unfold R.v27437, N.v27437.
  unfold R.v16463, N.v16463.
  rewrite !state_r1194_nr_5F1194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1194_nr_5F1194 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27438 (s : N.State) (i : N.Inputs) :
  R.v27438 (state s) (inputs i) = Zmod.unsigned (N.v27438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27438 s i)) at 1.
  unfold R.v27438, N.v27438.
  unfold R.v6, N.v6.
  rewrite !state_r1193_nr_5F1193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1193_nr_5F1193 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27439 (s : N.State) (i : N.Inputs) :
  R.v27439 (state s) (inputs i) = Zmod.unsigned (N.v27439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27439 s i)) at 1.
  unfold R.v27439, N.v27439.
  unfold R.v6, N.v6.
  rewrite !state_r1192_nr_5F1192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1192_nr_5F1192 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27440 (s : N.State) (i : N.Inputs) :
  R.v27440 (state s) (inputs i) = Zmod.unsigned (N.v27440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27440 s i)) at 1.
  unfold R.v27440, N.v27440.
  rewrite ?node_27438.
  rewrite ?node_27439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27441 (s : N.State) (i : N.Inputs) :
  R.v27441 (state s) (inputs i) = Zmod.unsigned (N.v27441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27441 s i)) at 1.
  unfold R.v27441, N.v27441.
  unfold R.v16484, N.v16484.
  rewrite ?node_27440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27442 (s : N.State) (i : N.Inputs) :
  R.v27442 (state s) (inputs i) = Zmod.unsigned (N.v27442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27442 s i)) at 1.
  unfold R.v27442, N.v27442.
  rewrite ?node_27435.
  rewrite ?node_27436.
  rewrite ?node_27437.
  rewrite ?node_27441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27443 (s : N.State) (i : N.Inputs) :
  R.v27443 (state s) (inputs i) = Zmod.unsigned (N.v27443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27443 s i)) at 1.
  unfold R.v27443, N.v27443.
  unfold R.v6, N.v6.
  rewrite ?node_27442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27444 (s : N.State) (i : N.Inputs) :
  R.v27444 (state s) (inputs i) = Zmod.unsigned (N.v27444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27444 s i)) at 1.
  unfold R.v27444, N.v27444.
  rewrite ?node_10612.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27445 (s : N.State) (i : N.Inputs) :
  R.v27445 (state s) (inputs i) = Zmod.unsigned (N.v27445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27445 s i)) at 1.
  unfold R.v27445, N.v27445.
  unfold R.v6, N.v6.
  rewrite ?node_10772.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27446 (s : N.State) (i : N.Inputs) :
  R.v27446 (state s) (inputs i) = Zmod.unsigned (N.v27446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27446 s i)) at 1.
  unfold R.v27446, N.v27446.
  unfold R.v6, N.v6.
  rewrite ?node_10837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27447 (s : N.State) (i : N.Inputs) :
  R.v27447 (state s) (inputs i) = Zmod.unsigned (N.v27447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27447 s i)) at 1.
  unfold R.v27447, N.v27447.
  rewrite ?node_27444.
  rewrite ?node_27445.
  rewrite ?node_27446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27448 (s : N.State) (i : N.Inputs) :
  R.v27448 (state s) (inputs i) = Zmod.unsigned (N.v27448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27448 s i)) at 1.
  unfold R.v27448, N.v27448.
  rewrite ?node_27443.
  rewrite ?node_27447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27449 (s : N.State) (i : N.Inputs) :
  R.v27449 (state s) (inputs i) = Zmod.unsigned (N.v27449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27449 s i)) at 1.
  unfold R.v27449, N.v27449.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27450 (s : N.State) (i : N.Inputs) :
  R.v27450 (state s) (inputs i) = Zmod.unsigned (N.v27450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27450 s i)) at 1.
  unfold R.v27450, N.v27450.
  unfold R.v16463, N.v16463.
  rewrite !state_r1194_nr_5F1194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1194_nr_5F1194 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27451 (s : N.State) (i : N.Inputs) :
  R.v27451 (state s) (inputs i) = Zmod.unsigned (N.v27451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27451 s i)) at 1.
  unfold R.v27451, N.v27451.
  unfold R.v6, N.v6.
  rewrite !state_r1193_nr_5F1193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1193_nr_5F1193 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27452 (s : N.State) (i : N.Inputs) :
  R.v27452 (state s) (inputs i) = Zmod.unsigned (N.v27452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27452 s i)) at 1.
  unfold R.v27452, N.v27452.
  unfold R.v6, N.v6.
  rewrite !state_r1192_nr_5F1192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1192_nr_5F1192 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27453 (s : N.State) (i : N.Inputs) :
  R.v27453 (state s) (inputs i) = Zmod.unsigned (N.v27453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27453 s i)) at 1.
  unfold R.v27453, N.v27453.
  rewrite ?node_27451.
  rewrite ?node_27452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27454 (s : N.State) (i : N.Inputs) :
  R.v27454 (state s) (inputs i) = Zmod.unsigned (N.v27454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27454 s i)) at 1.
  unfold R.v27454, N.v27454.
  unfold R.v16484, N.v16484.
  rewrite ?node_27453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27455 (s : N.State) (i : N.Inputs) :
  R.v27455 (state s) (inputs i) = Zmod.unsigned (N.v27455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27455 s i)) at 1.
  unfold R.v27455, N.v27455.
  rewrite ?node_27450.
  rewrite ?node_27454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27456 (s : N.State) (i : N.Inputs) :
  R.v27456 (state s) (inputs i) = Zmod.unsigned (N.v27456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27456 s i)) at 1.
  unfold R.v27456, N.v27456.
  unfold R.v6, N.v6.
  rewrite ?node_27455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27457 (s : N.State) (i : N.Inputs) :
  R.v27457 (state s) (inputs i) = Zmod.unsigned (N.v27457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27457 s i)) at 1.
  unfold R.v27457, N.v27457.
  rewrite ?node_10607.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27458 (s : N.State) (i : N.Inputs) :
  R.v27458 (state s) (inputs i) = Zmod.unsigned (N.v27458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27458 s i)) at 1.
  unfold R.v27458, N.v27458.
  unfold R.v6, N.v6.
  rewrite ?node_10772.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27459 (s : N.State) (i : N.Inputs) :
  R.v27459 (state s) (inputs i) = Zmod.unsigned (N.v27459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27459 s i)) at 1.
  unfold R.v27459, N.v27459.
  rewrite ?node_27457.
  rewrite ?node_27458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27460 (s : N.State) (i : N.Inputs) :
  R.v27460 (state s) (inputs i) = Zmod.unsigned (N.v27460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27460 s i)) at 1.
  unfold R.v27460, N.v27460.
  rewrite ?node_27456.
  rewrite ?node_27459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27461 (s : N.State) (i : N.Inputs) :
  R.v27461 (state s) (inputs i) = Zmod.unsigned (N.v27461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27461 s i)) at 1.
  unfold R.v27461, N.v27461.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27462 (s : N.State) (i : N.Inputs) :
  R.v27462 (state s) (inputs i) = Zmod.unsigned (N.v27462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27462 s i)) at 1.
  unfold R.v27462, N.v27462.
  rewrite ?node_10611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27463 (s : N.State) (i : N.Inputs) :
  R.v27463 (state s) (inputs i) = Zmod.unsigned (N.v27463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27463 s i)) at 1.
  unfold R.v27463, N.v27463.
  unfold R.v6, N.v6.
  rewrite !state_r1195_nr_5F1195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1195_nr_5F1195 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27464 (s : N.State) (i : N.Inputs) :
  R.v27464 (state s) (inputs i) = Zmod.unsigned (N.v27464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27464 s i)) at 1.
  unfold R.v27464, N.v27464.
  unfold R.v6, N.v6.
  rewrite ?node_10607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27465 (s : N.State) (i : N.Inputs) :
  R.v27465 (state s) (inputs i) = Zmod.unsigned (N.v27465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27465 s i)) at 1.
  unfold R.v27465, N.v27465.
  rewrite ?node_27463.
  rewrite ?node_27464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27466 (s : N.State) (i : N.Inputs) :
  R.v27466 (state s) (inputs i) = Zmod.unsigned (N.v27466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27466 s i)) at 1.
  unfold R.v27466, N.v27466.
  unfold R.v16484, N.v16484.
  rewrite ?node_27465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27467 (s : N.State) (i : N.Inputs) :
  R.v27467 (state s) (inputs i) = Zmod.unsigned (N.v27467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27467 s i)) at 1.
  unfold R.v27467, N.v27467.
  rewrite ?node_27462.
  rewrite ?node_27466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27468 (s : N.State) (i : N.Inputs) :
  R.v27468 (state s) (inputs i) = Zmod.unsigned (N.v27468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27468 s i)) at 1.
  unfold R.v27468, N.v27468.
  unfold R.v6, N.v6.
  rewrite ?node_27467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27469 (s : N.State) (i : N.Inputs) :
  R.v27469 (state s) (inputs i) = Zmod.unsigned (N.v27469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27469 s i)) at 1.
  unfold R.v27469, N.v27469.
  rewrite ?node_10612.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27470 (s : N.State) (i : N.Inputs) :
  R.v27470 (state s) (inputs i) = Zmod.unsigned (N.v27470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27470 s i)) at 1.
  unfold R.v27470, N.v27470.
  unfold R.v6, N.v6.
  rewrite ?node_10837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27471 (s : N.State) (i : N.Inputs) :
  R.v27471 (state s) (inputs i) = Zmod.unsigned (N.v27471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27471 s i)) at 1.
  unfold R.v27471, N.v27471.
  rewrite ?node_27469.
  rewrite ?node_27470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27472 (s : N.State) (i : N.Inputs) :
  R.v27472 (state s) (inputs i) = Zmod.unsigned (N.v27472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27472 s i)) at 1.
  unfold R.v27472, N.v27472.
  rewrite ?node_27468.
  rewrite ?node_27471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27473 (s : N.State) (i : N.Inputs) :
  R.v27473 (state s) (inputs i) = Zmod.unsigned (N.v27473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27473 s i)) at 1.
  unfold R.v27473, N.v27473.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27474 (s : N.State) (i : N.Inputs) :
  R.v27474 (state s) (inputs i) = Zmod.unsigned (N.v27474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27474 s i)) at 1.
  unfold R.v27474, N.v27474.
  rewrite ?node_10619.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27475 (s : N.State) (i : N.Inputs) :
  R.v27475 (state s) (inputs i) = Zmod.unsigned (N.v27475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27475 s i)) at 1.
  unfold R.v27475, N.v27475.
  unfold R.v16463, N.v16463.
  rewrite !state_r1199_nr_5F1199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1199_nr_5F1199 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27476 (s : N.State) (i : N.Inputs) :
  R.v27476 (state s) (inputs i) = Zmod.unsigned (N.v27476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27476 s i)) at 1.
  unfold R.v27476, N.v27476.
  unfold R.v16463, N.v16463.
  rewrite !state_r1198_nr_5F1198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1198_nr_5F1198 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27477 (s : N.State) (i : N.Inputs) :
  R.v27477 (state s) (inputs i) = Zmod.unsigned (N.v27477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27477 s i)) at 1.
  unfold R.v27477, N.v27477.
  unfold R.v6, N.v6.
  rewrite !state_r1197_nr_5F1197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1197_nr_5F1197 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27478 (s : N.State) (i : N.Inputs) :
  R.v27478 (state s) (inputs i) = Zmod.unsigned (N.v27478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27478 s i)) at 1.
  unfold R.v27478, N.v27478.
  unfold R.v6, N.v6.
  rewrite !state_r1196_nr_5F1196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1196_nr_5F1196 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27479 (s : N.State) (i : N.Inputs) :
  R.v27479 (state s) (inputs i) = Zmod.unsigned (N.v27479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27479 s i)) at 1.
  unfold R.v27479, N.v27479.
  rewrite ?node_27477.
  rewrite ?node_27478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27480 (s : N.State) (i : N.Inputs) :
  R.v27480 (state s) (inputs i) = Zmod.unsigned (N.v27480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27480 s i)) at 1.
  unfold R.v27480, N.v27480.
  unfold R.v16484, N.v16484.
  rewrite ?node_27479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27481 (s : N.State) (i : N.Inputs) :
  R.v27481 (state s) (inputs i) = Zmod.unsigned (N.v27481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27481 s i)) at 1.
  unfold R.v27481, N.v27481.
  rewrite ?node_27474.
  rewrite ?node_27475.
  rewrite ?node_27476.
  rewrite ?node_27480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27482 (s : N.State) (i : N.Inputs) :
  R.v27482 (state s) (inputs i) = Zmod.unsigned (N.v27482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27482 s i)) at 1.
  unfold R.v27482, N.v27482.
  unfold R.v6, N.v6.
  rewrite ?node_27481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27483 (s : N.State) (i : N.Inputs) :
  R.v27483 (state s) (inputs i) = Zmod.unsigned (N.v27483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27483 s i)) at 1.
  unfold R.v27483, N.v27483.
  rewrite ?node_10620.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27484 (s : N.State) (i : N.Inputs) :
  R.v27484 (state s) (inputs i) = Zmod.unsigned (N.v27484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27484 s i)) at 1.
  unfold R.v27484, N.v27484.
  unfold R.v6, N.v6.
  rewrite ?node_10780.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27485 (s : N.State) (i : N.Inputs) :
  R.v27485 (state s) (inputs i) = Zmod.unsigned (N.v27485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27485 s i)) at 1.
  unfold R.v27485, N.v27485.
  unfold R.v6, N.v6.
  rewrite ?node_10841.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27486 (s : N.State) (i : N.Inputs) :
  R.v27486 (state s) (inputs i) = Zmod.unsigned (N.v27486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27486 s i)) at 1.
  unfold R.v27486, N.v27486.
  rewrite ?node_27483.
  rewrite ?node_27484.
  rewrite ?node_27485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27487 (s : N.State) (i : N.Inputs) :
  R.v27487 (state s) (inputs i) = Zmod.unsigned (N.v27487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27487 s i)) at 1.
  unfold R.v27487, N.v27487.
  rewrite ?node_27482.
  rewrite ?node_27486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27488 (s : N.State) (i : N.Inputs) :
  R.v27488 (state s) (inputs i) = Zmod.unsigned (N.v27488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27488 s i)) at 1.
  unfold R.v27488, N.v27488.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27489 (s : N.State) (i : N.Inputs) :
  R.v27489 (state s) (inputs i) = Zmod.unsigned (N.v27489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27489 s i)) at 1.
  unfold R.v27489, N.v27489.
  unfold R.v16463, N.v16463.
  rewrite !state_r1198_nr_5F1198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1198_nr_5F1198 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27490 (s : N.State) (i : N.Inputs) :
  R.v27490 (state s) (inputs i) = Zmod.unsigned (N.v27490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27490 s i)) at 1.
  unfold R.v27490, N.v27490.
  unfold R.v6, N.v6.
  rewrite !state_r1197_nr_5F1197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1197_nr_5F1197 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27491 (s : N.State) (i : N.Inputs) :
  R.v27491 (state s) (inputs i) = Zmod.unsigned (N.v27491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27491 s i)) at 1.
  unfold R.v27491, N.v27491.
  unfold R.v6, N.v6.
  rewrite !state_r1196_nr_5F1196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1196_nr_5F1196 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27492 (s : N.State) (i : N.Inputs) :
  R.v27492 (state s) (inputs i) = Zmod.unsigned (N.v27492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27492 s i)) at 1.
  unfold R.v27492, N.v27492.
  rewrite ?node_27490.
  rewrite ?node_27491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27493 (s : N.State) (i : N.Inputs) :
  R.v27493 (state s) (inputs i) = Zmod.unsigned (N.v27493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27493 s i)) at 1.
  unfold R.v27493, N.v27493.
  unfold R.v16484, N.v16484.
  rewrite ?node_27492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27494 (s : N.State) (i : N.Inputs) :
  R.v27494 (state s) (inputs i) = Zmod.unsigned (N.v27494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27494 s i)) at 1.
  unfold R.v27494, N.v27494.
  rewrite ?node_27489.
  rewrite ?node_27493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27495 (s : N.State) (i : N.Inputs) :
  R.v27495 (state s) (inputs i) = Zmod.unsigned (N.v27495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27495 s i)) at 1.
  unfold R.v27495, N.v27495.
  unfold R.v6, N.v6.
  rewrite ?node_27494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27496 (s : N.State) (i : N.Inputs) :
  R.v27496 (state s) (inputs i) = Zmod.unsigned (N.v27496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27496 s i)) at 1.
  unfold R.v27496, N.v27496.
  rewrite ?node_10615.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27497 (s : N.State) (i : N.Inputs) :
  R.v27497 (state s) (inputs i) = Zmod.unsigned (N.v27497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27497 s i)) at 1.
  unfold R.v27497, N.v27497.
  unfold R.v6, N.v6.
  rewrite ?node_10780.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27498 (s : N.State) (i : N.Inputs) :
  R.v27498 (state s) (inputs i) = Zmod.unsigned (N.v27498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27498 s i)) at 1.
  unfold R.v27498, N.v27498.
  rewrite ?node_27496.
  rewrite ?node_27497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27499 (s : N.State) (i : N.Inputs) :
  R.v27499 (state s) (inputs i) = Zmod.unsigned (N.v27499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27499 s i)) at 1.
  unfold R.v27499, N.v27499.
  rewrite ?node_27495.
  rewrite ?node_27498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27500 (s : N.State) (i : N.Inputs) :
  R.v27500 (state s) (inputs i) = Zmod.unsigned (N.v27500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27500 s i)) at 1.
  unfold R.v27500, N.v27500.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27501 (s : N.State) (i : N.Inputs) :
  R.v27501 (state s) (inputs i) = Zmod.unsigned (N.v27501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27501 s i)) at 1.
  unfold R.v27501, N.v27501.
  rewrite ?node_10619.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27502 (s : N.State) (i : N.Inputs) :
  R.v27502 (state s) (inputs i) = Zmod.unsigned (N.v27502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27502 s i)) at 1.
  unfold R.v27502, N.v27502.
  unfold R.v6, N.v6.
  rewrite !state_r1199_nr_5F1199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1199_nr_5F1199 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27503 (s : N.State) (i : N.Inputs) :
  R.v27503 (state s) (inputs i) = Zmod.unsigned (N.v27503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27503 s i)) at 1.
  unfold R.v27503, N.v27503.
  unfold R.v6, N.v6.
  rewrite ?node_10615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27504 (s : N.State) (i : N.Inputs) :
  R.v27504 (state s) (inputs i) = Zmod.unsigned (N.v27504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27504 s i)) at 1.
  unfold R.v27504, N.v27504.
  rewrite ?node_27502.
  rewrite ?node_27503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27505 (s : N.State) (i : N.Inputs) :
  R.v27505 (state s) (inputs i) = Zmod.unsigned (N.v27505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27505 s i)) at 1.
  unfold R.v27505, N.v27505.
  unfold R.v16484, N.v16484.
  rewrite ?node_27504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27506 (s : N.State) (i : N.Inputs) :
  R.v27506 (state s) (inputs i) = Zmod.unsigned (N.v27506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27506 s i)) at 1.
  unfold R.v27506, N.v27506.
  rewrite ?node_27501.
  rewrite ?node_27505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27507 (s : N.State) (i : N.Inputs) :
  R.v27507 (state s) (inputs i) = Zmod.unsigned (N.v27507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27507 s i)) at 1.
  unfold R.v27507, N.v27507.
  unfold R.v6, N.v6.
  rewrite ?node_27506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27508 (s : N.State) (i : N.Inputs) :
  R.v27508 (state s) (inputs i) = Zmod.unsigned (N.v27508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27508 s i)) at 1.
  unfold R.v27508, N.v27508.
  rewrite ?node_10620.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27509 (s : N.State) (i : N.Inputs) :
  R.v27509 (state s) (inputs i) = Zmod.unsigned (N.v27509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27509 s i)) at 1.
  unfold R.v27509, N.v27509.
  unfold R.v6, N.v6.
  rewrite ?node_10841.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27510 (s : N.State) (i : N.Inputs) :
  R.v27510 (state s) (inputs i) = Zmod.unsigned (N.v27510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27510 s i)) at 1.
  unfold R.v27510, N.v27510.
  rewrite ?node_27508.
  rewrite ?node_27509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27511 (s : N.State) (i : N.Inputs) :
  R.v27511 (state s) (inputs i) = Zmod.unsigned (N.v27511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27511 s i)) at 1.
  unfold R.v27511, N.v27511.
  rewrite ?node_27507.
  rewrite ?node_27510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27512 (s : N.State) (i : N.Inputs) :
  R.v27512 (state s) (inputs i) = Zmod.unsigned (N.v27512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27512 s i)) at 1.
  unfold R.v27512, N.v27512.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27513 (s : N.State) (i : N.Inputs) :
  R.v27513 (state s) (inputs i) = Zmod.unsigned (N.v27513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27513 s i)) at 1.
  unfold R.v27513, N.v27513.
  rewrite ?node_10627.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27514 (s : N.State) (i : N.Inputs) :
  R.v27514 (state s) (inputs i) = Zmod.unsigned (N.v27514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27514 s i)) at 1.
  unfold R.v27514, N.v27514.
  unfold R.v16463, N.v16463.
  rewrite !state_r1203_nr_5F1203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1203_nr_5F1203 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27515 (s : N.State) (i : N.Inputs) :
  R.v27515 (state s) (inputs i) = Zmod.unsigned (N.v27515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27515 s i)) at 1.
  unfold R.v27515, N.v27515.
  unfold R.v16463, N.v16463.
  rewrite !state_r1202_nr_5F1202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1202_nr_5F1202 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27516 (s : N.State) (i : N.Inputs) :
  R.v27516 (state s) (inputs i) = Zmod.unsigned (N.v27516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27516 s i)) at 1.
  unfold R.v27516, N.v27516.
  unfold R.v6, N.v6.
  rewrite !state_r1201_nr_5F1201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1201_nr_5F1201 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27517 (s : N.State) (i : N.Inputs) :
  R.v27517 (state s) (inputs i) = Zmod.unsigned (N.v27517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27517 s i)) at 1.
  unfold R.v27517, N.v27517.
  unfold R.v6, N.v6.
  rewrite !state_r1200_nr_5F1200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1200_nr_5F1200 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27518 (s : N.State) (i : N.Inputs) :
  R.v27518 (state s) (inputs i) = Zmod.unsigned (N.v27518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27518 s i)) at 1.
  unfold R.v27518, N.v27518.
  rewrite ?node_27516.
  rewrite ?node_27517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27519 (s : N.State) (i : N.Inputs) :
  R.v27519 (state s) (inputs i) = Zmod.unsigned (N.v27519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27519 s i)) at 1.
  unfold R.v27519, N.v27519.
  unfold R.v16484, N.v16484.
  rewrite ?node_27518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27520 (s : N.State) (i : N.Inputs) :
  R.v27520 (state s) (inputs i) = Zmod.unsigned (N.v27520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27520 s i)) at 1.
  unfold R.v27520, N.v27520.
  rewrite ?node_27513.
  rewrite ?node_27514.
  rewrite ?node_27515.
  rewrite ?node_27519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27521 (s : N.State) (i : N.Inputs) :
  R.v27521 (state s) (inputs i) = Zmod.unsigned (N.v27521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27521 s i)) at 1.
  unfold R.v27521, N.v27521.
  unfold R.v6, N.v6.
  rewrite ?node_27520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27522 (s : N.State) (i : N.Inputs) :
  R.v27522 (state s) (inputs i) = Zmod.unsigned (N.v27522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27522 s i)) at 1.
  unfold R.v27522, N.v27522.
  rewrite ?node_10628.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27523 (s : N.State) (i : N.Inputs) :
  R.v27523 (state s) (inputs i) = Zmod.unsigned (N.v27523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27523 s i)) at 1.
  unfold R.v27523, N.v27523.
  unfold R.v6, N.v6.
  rewrite ?node_10788.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27524 (s : N.State) (i : N.Inputs) :
  R.v27524 (state s) (inputs i) = Zmod.unsigned (N.v27524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27524 s i)) at 1.
  unfold R.v27524, N.v27524.
  unfold R.v6, N.v6.
  rewrite ?node_10850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27525 (s : N.State) (i : N.Inputs) :
  R.v27525 (state s) (inputs i) = Zmod.unsigned (N.v27525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27525 s i)) at 1.
  unfold R.v27525, N.v27525.
  rewrite ?node_27522.
  rewrite ?node_27523.
  rewrite ?node_27524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27526 (s : N.State) (i : N.Inputs) :
  R.v27526 (state s) (inputs i) = Zmod.unsigned (N.v27526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27526 s i)) at 1.
  unfold R.v27526, N.v27526.
  rewrite ?node_27521.
  rewrite ?node_27525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27527 (s : N.State) (i : N.Inputs) :
  R.v27527 (state s) (inputs i) = Zmod.unsigned (N.v27527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27527 s i)) at 1.
  unfold R.v27527, N.v27527.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27528 (s : N.State) (i : N.Inputs) :
  R.v27528 (state s) (inputs i) = Zmod.unsigned (N.v27528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27528 s i)) at 1.
  unfold R.v27528, N.v27528.
  unfold R.v16463, N.v16463.
  rewrite !state_r1202_nr_5F1202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1202_nr_5F1202 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27529 (s : N.State) (i : N.Inputs) :
  R.v27529 (state s) (inputs i) = Zmod.unsigned (N.v27529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27529 s i)) at 1.
  unfold R.v27529, N.v27529.
  unfold R.v6, N.v6.
  rewrite !state_r1201_nr_5F1201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1201_nr_5F1201 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27530 (s : N.State) (i : N.Inputs) :
  R.v27530 (state s) (inputs i) = Zmod.unsigned (N.v27530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27530 s i)) at 1.
  unfold R.v27530, N.v27530.
  unfold R.v6, N.v6.
  rewrite !state_r1200_nr_5F1200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1200_nr_5F1200 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27531 (s : N.State) (i : N.Inputs) :
  R.v27531 (state s) (inputs i) = Zmod.unsigned (N.v27531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27531 s i)) at 1.
  unfold R.v27531, N.v27531.
  rewrite ?node_27529.
  rewrite ?node_27530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27532 (s : N.State) (i : N.Inputs) :
  R.v27532 (state s) (inputs i) = Zmod.unsigned (N.v27532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27532 s i)) at 1.
  unfold R.v27532, N.v27532.
  unfold R.v16484, N.v16484.
  rewrite ?node_27531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27533 (s : N.State) (i : N.Inputs) :
  R.v27533 (state s) (inputs i) = Zmod.unsigned (N.v27533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27533 s i)) at 1.
  unfold R.v27533, N.v27533.
  rewrite ?node_27528.
  rewrite ?node_27532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27534 (s : N.State) (i : N.Inputs) :
  R.v27534 (state s) (inputs i) = Zmod.unsigned (N.v27534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27534 s i)) at 1.
  unfold R.v27534, N.v27534.
  unfold R.v6, N.v6.
  rewrite ?node_27533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27535 (s : N.State) (i : N.Inputs) :
  R.v27535 (state s) (inputs i) = Zmod.unsigned (N.v27535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27535 s i)) at 1.
  unfold R.v27535, N.v27535.
  rewrite ?node_10623.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27536 (s : N.State) (i : N.Inputs) :
  R.v27536 (state s) (inputs i) = Zmod.unsigned (N.v27536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27536 s i)) at 1.
  unfold R.v27536, N.v27536.
  unfold R.v6, N.v6.
  rewrite ?node_10788.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27537 (s : N.State) (i : N.Inputs) :
  R.v27537 (state s) (inputs i) = Zmod.unsigned (N.v27537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27537 s i)) at 1.
  unfold R.v27537, N.v27537.
  rewrite ?node_27535.
  rewrite ?node_27536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27538 (s : N.State) (i : N.Inputs) :
  R.v27538 (state s) (inputs i) = Zmod.unsigned (N.v27538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27538 s i)) at 1.
  unfold R.v27538, N.v27538.
  rewrite ?node_27534.
  rewrite ?node_27537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27539 (s : N.State) (i : N.Inputs) :
  R.v27539 (state s) (inputs i) = Zmod.unsigned (N.v27539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27539 s i)) at 1.
  unfold R.v27539, N.v27539.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27540 (s : N.State) (i : N.Inputs) :
  R.v27540 (state s) (inputs i) = Zmod.unsigned (N.v27540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27540 s i)) at 1.
  unfold R.v27540, N.v27540.
  rewrite ?node_10627.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27541 (s : N.State) (i : N.Inputs) :
  R.v27541 (state s) (inputs i) = Zmod.unsigned (N.v27541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27541 s i)) at 1.
  unfold R.v27541, N.v27541.
  unfold R.v6, N.v6.
  rewrite !state_r1203_nr_5F1203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1203_nr_5F1203 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27542 (s : N.State) (i : N.Inputs) :
  R.v27542 (state s) (inputs i) = Zmod.unsigned (N.v27542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27542 s i)) at 1.
  unfold R.v27542, N.v27542.
  unfold R.v6, N.v6.
  rewrite ?node_10623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27543 (s : N.State) (i : N.Inputs) :
  R.v27543 (state s) (inputs i) = Zmod.unsigned (N.v27543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27543 s i)) at 1.
  unfold R.v27543, N.v27543.
  rewrite ?node_27541.
  rewrite ?node_27542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27544 (s : N.State) (i : N.Inputs) :
  R.v27544 (state s) (inputs i) = Zmod.unsigned (N.v27544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27544 s i)) at 1.
  unfold R.v27544, N.v27544.
  unfold R.v16484, N.v16484.
  rewrite ?node_27543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27545 (s : N.State) (i : N.Inputs) :
  R.v27545 (state s) (inputs i) = Zmod.unsigned (N.v27545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27545 s i)) at 1.
  unfold R.v27545, N.v27545.
  rewrite ?node_27540.
  rewrite ?node_27544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27546 (s : N.State) (i : N.Inputs) :
  R.v27546 (state s) (inputs i) = Zmod.unsigned (N.v27546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27546 s i)) at 1.
  unfold R.v27546, N.v27546.
  unfold R.v6, N.v6.
  rewrite ?node_27545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27547 (s : N.State) (i : N.Inputs) :
  R.v27547 (state s) (inputs i) = Zmod.unsigned (N.v27547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27547 s i)) at 1.
  unfold R.v27547, N.v27547.
  rewrite ?node_10628.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27548 (s : N.State) (i : N.Inputs) :
  R.v27548 (state s) (inputs i) = Zmod.unsigned (N.v27548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27548 s i)) at 1.
  unfold R.v27548, N.v27548.
  unfold R.v6, N.v6.
  rewrite ?node_10850.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27549 (s : N.State) (i : N.Inputs) :
  R.v27549 (state s) (inputs i) = Zmod.unsigned (N.v27549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27549 s i)) at 1.
  unfold R.v27549, N.v27549.
  rewrite ?node_27547.
  rewrite ?node_27548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27550 (s : N.State) (i : N.Inputs) :
  R.v27550 (state s) (inputs i) = Zmod.unsigned (N.v27550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27550 s i)) at 1.
  unfold R.v27550, N.v27550.
  rewrite ?node_27546.
  rewrite ?node_27549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27551 (s : N.State) (i : N.Inputs) :
  R.v27551 (state s) (inputs i) = Zmod.unsigned (N.v27551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27551 s i)) at 1.
  unfold R.v27551, N.v27551.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27552 (s : N.State) (i : N.Inputs) :
  R.v27552 (state s) (inputs i) = Zmod.unsigned (N.v27552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27552 s i)) at 1.
  unfold R.v27552, N.v27552.
  rewrite ?node_10639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27553 (s : N.State) (i : N.Inputs) :
  R.v27553 (state s) (inputs i) = Zmod.unsigned (N.v27553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27553 s i)) at 1.
  unfold R.v27553, N.v27553.
  unfold R.v16463, N.v16463.
  rewrite !state_r1207_nr_5F1207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1207_nr_5F1207 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27554 (s : N.State) (i : N.Inputs) :
  R.v27554 (state s) (inputs i) = Zmod.unsigned (N.v27554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27554 s i)) at 1.
  unfold R.v27554, N.v27554.
  unfold R.v16463, N.v16463.
  rewrite !state_r1206_nr_5F1206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1206_nr_5F1206 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27555 (s : N.State) (i : N.Inputs) :
  R.v27555 (state s) (inputs i) = Zmod.unsigned (N.v27555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27555 s i)) at 1.
  unfold R.v27555, N.v27555.
  unfold R.v6, N.v6.
  rewrite !state_r1205_nr_5F1205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1205_nr_5F1205 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27556 (s : N.State) (i : N.Inputs) :
  R.v27556 (state s) (inputs i) = Zmod.unsigned (N.v27556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27556 s i)) at 1.
  unfold R.v27556, N.v27556.
  unfold R.v6, N.v6.
  rewrite !state_r1204_nr_5F1204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1204_nr_5F1204 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27557 (s : N.State) (i : N.Inputs) :
  R.v27557 (state s) (inputs i) = Zmod.unsigned (N.v27557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27557 s i)) at 1.
  unfold R.v27557, N.v27557.
  rewrite ?node_27555.
  rewrite ?node_27556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27558 (s : N.State) (i : N.Inputs) :
  R.v27558 (state s) (inputs i) = Zmod.unsigned (N.v27558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27558 s i)) at 1.
  unfold R.v27558, N.v27558.
  unfold R.v16484, N.v16484.
  rewrite ?node_27557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27559 (s : N.State) (i : N.Inputs) :
  R.v27559 (state s) (inputs i) = Zmod.unsigned (N.v27559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27559 s i)) at 1.
  unfold R.v27559, N.v27559.
  rewrite ?node_27552.
  rewrite ?node_27553.
  rewrite ?node_27554.
  rewrite ?node_27558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27560 (s : N.State) (i : N.Inputs) :
  R.v27560 (state s) (inputs i) = Zmod.unsigned (N.v27560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27560 s i)) at 1.
  unfold R.v27560, N.v27560.
  unfold R.v6, N.v6.
  rewrite ?node_27559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27561 (s : N.State) (i : N.Inputs) :
  R.v27561 (state s) (inputs i) = Zmod.unsigned (N.v27561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27561 s i)) at 1.
  unfold R.v27561, N.v27561.
  rewrite ?node_10640.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27562 (s : N.State) (i : N.Inputs) :
  R.v27562 (state s) (inputs i) = Zmod.unsigned (N.v27562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27562 s i)) at 1.
  unfold R.v27562, N.v27562.
  unfold R.v6, N.v6.
  rewrite ?node_10800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27563 (s : N.State) (i : N.Inputs) :
  R.v27563 (state s) (inputs i) = Zmod.unsigned (N.v27563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27563 s i)) at 1.
  unfold R.v27563, N.v27563.
  unfold R.v6, N.v6.
  rewrite ?node_10853.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27564 (s : N.State) (i : N.Inputs) :
  R.v27564 (state s) (inputs i) = Zmod.unsigned (N.v27564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27564 s i)) at 1.
  unfold R.v27564, N.v27564.
  rewrite ?node_27561.
  rewrite ?node_27562.
  rewrite ?node_27563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27565 (s : N.State) (i : N.Inputs) :
  R.v27565 (state s) (inputs i) = Zmod.unsigned (N.v27565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27565 s i)) at 1.
  unfold R.v27565, N.v27565.
  rewrite ?node_27560.
  rewrite ?node_27564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27566 (s : N.State) (i : N.Inputs) :
  R.v27566 (state s) (inputs i) = Zmod.unsigned (N.v27566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27566 s i)) at 1.
  unfold R.v27566, N.v27566.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27567 (s : N.State) (i : N.Inputs) :
  R.v27567 (state s) (inputs i) = Zmod.unsigned (N.v27567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27567 s i)) at 1.
  unfold R.v27567, N.v27567.
  unfold R.v16463, N.v16463.
  rewrite !state_r1206_nr_5F1206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1206_nr_5F1206 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27568 (s : N.State) (i : N.Inputs) :
  R.v27568 (state s) (inputs i) = Zmod.unsigned (N.v27568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27568 s i)) at 1.
  unfold R.v27568, N.v27568.
  unfold R.v6, N.v6.
  rewrite !state_r1205_nr_5F1205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1205_nr_5F1205 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27569 (s : N.State) (i : N.Inputs) :
  R.v27569 (state s) (inputs i) = Zmod.unsigned (N.v27569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27569 s i)) at 1.
  unfold R.v27569, N.v27569.
  unfold R.v6, N.v6.
  rewrite !state_r1204_nr_5F1204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1204_nr_5F1204 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27570 (s : N.State) (i : N.Inputs) :
  R.v27570 (state s) (inputs i) = Zmod.unsigned (N.v27570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27570 s i)) at 1.
  unfold R.v27570, N.v27570.
  rewrite ?node_27568.
  rewrite ?node_27569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27571 (s : N.State) (i : N.Inputs) :
  R.v27571 (state s) (inputs i) = Zmod.unsigned (N.v27571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27571 s i)) at 1.
  unfold R.v27571, N.v27571.
  unfold R.v16484, N.v16484.
  rewrite ?node_27570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27572 (s : N.State) (i : N.Inputs) :
  R.v27572 (state s) (inputs i) = Zmod.unsigned (N.v27572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27572 s i)) at 1.
  unfold R.v27572, N.v27572.
  rewrite ?node_27567.
  rewrite ?node_27571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27573 (s : N.State) (i : N.Inputs) :
  R.v27573 (state s) (inputs i) = Zmod.unsigned (N.v27573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27573 s i)) at 1.
  unfold R.v27573, N.v27573.
  unfold R.v6, N.v6.
  rewrite ?node_27572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27574 (s : N.State) (i : N.Inputs) :
  R.v27574 (state s) (inputs i) = Zmod.unsigned (N.v27574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27574 s i)) at 1.
  unfold R.v27574, N.v27574.
  rewrite ?node_10635.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27575 (s : N.State) (i : N.Inputs) :
  R.v27575 (state s) (inputs i) = Zmod.unsigned (N.v27575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27575 s i)) at 1.
  unfold R.v27575, N.v27575.
  unfold R.v6, N.v6.
  rewrite ?node_10800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27576 (s : N.State) (i : N.Inputs) :
  R.v27576 (state s) (inputs i) = Zmod.unsigned (N.v27576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27576 s i)) at 1.
  unfold R.v27576, N.v27576.
  rewrite ?node_27574.
  rewrite ?node_27575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27577 (s : N.State) (i : N.Inputs) :
  R.v27577 (state s) (inputs i) = Zmod.unsigned (N.v27577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27577 s i)) at 1.
  unfold R.v27577, N.v27577.
  rewrite ?node_27573.
  rewrite ?node_27576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27578 (s : N.State) (i : N.Inputs) :
  R.v27578 (state s) (inputs i) = Zmod.unsigned (N.v27578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27578 s i)) at 1.
  unfold R.v27578, N.v27578.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27579 (s : N.State) (i : N.Inputs) :
  R.v27579 (state s) (inputs i) = Zmod.unsigned (N.v27579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27579 s i)) at 1.
  unfold R.v27579, N.v27579.
  rewrite ?node_10639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27580 (s : N.State) (i : N.Inputs) :
  R.v27580 (state s) (inputs i) = Zmod.unsigned (N.v27580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27580 s i)) at 1.
  unfold R.v27580, N.v27580.
  unfold R.v6, N.v6.
  rewrite !state_r1207_nr_5F1207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1207_nr_5F1207 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27581 (s : N.State) (i : N.Inputs) :
  R.v27581 (state s) (inputs i) = Zmod.unsigned (N.v27581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27581 s i)) at 1.
  unfold R.v27581, N.v27581.
  unfold R.v6, N.v6.
  rewrite ?node_10635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27582 (s : N.State) (i : N.Inputs) :
  R.v27582 (state s) (inputs i) = Zmod.unsigned (N.v27582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27582 s i)) at 1.
  unfold R.v27582, N.v27582.
  rewrite ?node_27580.
  rewrite ?node_27581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27583 (s : N.State) (i : N.Inputs) :
  R.v27583 (state s) (inputs i) = Zmod.unsigned (N.v27583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27583 s i)) at 1.
  unfold R.v27583, N.v27583.
  unfold R.v16484, N.v16484.
  rewrite ?node_27582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27584 (s : N.State) (i : N.Inputs) :
  R.v27584 (state s) (inputs i) = Zmod.unsigned (N.v27584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27584 s i)) at 1.
  unfold R.v27584, N.v27584.
  rewrite ?node_27579.
  rewrite ?node_27583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27585 (s : N.State) (i : N.Inputs) :
  R.v27585 (state s) (inputs i) = Zmod.unsigned (N.v27585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27585 s i)) at 1.
  unfold R.v27585, N.v27585.
  unfold R.v6, N.v6.
  rewrite ?node_27584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27586 (s : N.State) (i : N.Inputs) :
  R.v27586 (state s) (inputs i) = Zmod.unsigned (N.v27586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27586 s i)) at 1.
  unfold R.v27586, N.v27586.
  rewrite ?node_10640.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27587 (s : N.State) (i : N.Inputs) :
  R.v27587 (state s) (inputs i) = Zmod.unsigned (N.v27587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27587 s i)) at 1.
  unfold R.v27587, N.v27587.
  unfold R.v6, N.v6.
  rewrite ?node_10853.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27588 (s : N.State) (i : N.Inputs) :
  R.v27588 (state s) (inputs i) = Zmod.unsigned (N.v27588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27588 s i)) at 1.
  unfold R.v27588, N.v27588.
  rewrite ?node_27586.
  rewrite ?node_27587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27589 (s : N.State) (i : N.Inputs) :
  R.v27589 (state s) (inputs i) = Zmod.unsigned (N.v27589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27589 s i)) at 1.
  unfold R.v27589, N.v27589.
  rewrite ?node_27585.
  rewrite ?node_27588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27590 (s : N.State) (i : N.Inputs) :
  R.v27590 (state s) (inputs i) = Zmod.unsigned (N.v27590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27590 s i)) at 1.
  unfold R.v27590, N.v27590.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27591 (s : N.State) (i : N.Inputs) :
  R.v27591 (state s) (inputs i) = Zmod.unsigned (N.v27591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27591 s i)) at 1.
  unfold R.v27591, N.v27591.
  rewrite ?node_10646.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27592 (s : N.State) (i : N.Inputs) :
  R.v27592 (state s) (inputs i) = Zmod.unsigned (N.v27592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27592 s i)) at 1.
  unfold R.v27592, N.v27592.
  unfold R.v16463, N.v16463.
  rewrite !state_r1211_nr_5F1211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1211_nr_5F1211 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27593 (s : N.State) (i : N.Inputs) :
  R.v27593 (state s) (inputs i) = Zmod.unsigned (N.v27593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27593 s i)) at 1.
  unfold R.v27593, N.v27593.
  unfold R.v16463, N.v16463.
  rewrite !state_r1210_nr_5F1210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1210_nr_5F1210 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27594 (s : N.State) (i : N.Inputs) :
  R.v27594 (state s) (inputs i) = Zmod.unsigned (N.v27594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27594 s i)) at 1.
  unfold R.v27594, N.v27594.
  unfold R.v6, N.v6.
  rewrite !state_r1209_nr_5F1209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1209_nr_5F1209 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27595 (s : N.State) (i : N.Inputs) :
  R.v27595 (state s) (inputs i) = Zmod.unsigned (N.v27595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27595 s i)) at 1.
  unfold R.v27595, N.v27595.
  unfold R.v6, N.v6.
  rewrite !state_r1208_nr_5F1208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1208_nr_5F1208 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27596 (s : N.State) (i : N.Inputs) :
  R.v27596 (state s) (inputs i) = Zmod.unsigned (N.v27596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27596 s i)) at 1.
  unfold R.v27596, N.v27596.
  rewrite ?node_27594.
  rewrite ?node_27595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27597 (s : N.State) (i : N.Inputs) :
  R.v27597 (state s) (inputs i) = Zmod.unsigned (N.v27597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27597 s i)) at 1.
  unfold R.v27597, N.v27597.
  unfold R.v16484, N.v16484.
  rewrite ?node_27596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27598 (s : N.State) (i : N.Inputs) :
  R.v27598 (state s) (inputs i) = Zmod.unsigned (N.v27598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27598 s i)) at 1.
  unfold R.v27598, N.v27598.
  rewrite ?node_27591.
  rewrite ?node_27592.
  rewrite ?node_27593.
  rewrite ?node_27597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27599 (s : N.State) (i : N.Inputs) :
  R.v27599 (state s) (inputs i) = Zmod.unsigned (N.v27599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27599 s i)) at 1.
  unfold R.v27599, N.v27599.
  unfold R.v6, N.v6.
  rewrite ?node_27598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27600 (s : N.State) (i : N.Inputs) :
  R.v27600 (state s) (inputs i) = Zmod.unsigned (N.v27600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27600 s i)) at 1.
  unfold R.v27600, N.v27600.
  rewrite ?node_10647.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27601 (s : N.State) (i : N.Inputs) :
  R.v27601 (state s) (inputs i) = Zmod.unsigned (N.v27601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27601 s i)) at 1.
  unfold R.v27601, N.v27601.
  unfold R.v6, N.v6.
  rewrite ?node_10807.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27602 (s : N.State) (i : N.Inputs) :
  R.v27602 (state s) (inputs i) = Zmod.unsigned (N.v27602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27602 s i)) at 1.
  unfold R.v27602, N.v27602.
  unfold R.v6, N.v6.
  rewrite ?node_10857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27603 (s : N.State) (i : N.Inputs) :
  R.v27603 (state s) (inputs i) = Zmod.unsigned (N.v27603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27603 s i)) at 1.
  unfold R.v27603, N.v27603.
  rewrite ?node_27600.
  rewrite ?node_27601.
  rewrite ?node_27602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27604 (s : N.State) (i : N.Inputs) :
  R.v27604 (state s) (inputs i) = Zmod.unsigned (N.v27604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27604 s i)) at 1.
  unfold R.v27604, N.v27604.
  rewrite ?node_27599.
  rewrite ?node_27603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27605 (s : N.State) (i : N.Inputs) :
  R.v27605 (state s) (inputs i) = Zmod.unsigned (N.v27605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27605 s i)) at 1.
  unfold R.v27605, N.v27605.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27606 (s : N.State) (i : N.Inputs) :
  R.v27606 (state s) (inputs i) = Zmod.unsigned (N.v27606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27606 s i)) at 1.
  unfold R.v27606, N.v27606.
  unfold R.v16463, N.v16463.
  rewrite !state_r1210_nr_5F1210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1210_nr_5F1210 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27607 (s : N.State) (i : N.Inputs) :
  R.v27607 (state s) (inputs i) = Zmod.unsigned (N.v27607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27607 s i)) at 1.
  unfold R.v27607, N.v27607.
  unfold R.v6, N.v6.
  rewrite !state_r1209_nr_5F1209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1209_nr_5F1209 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27608 (s : N.State) (i : N.Inputs) :
  R.v27608 (state s) (inputs i) = Zmod.unsigned (N.v27608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27608 s i)) at 1.
  unfold R.v27608, N.v27608.
  unfold R.v6, N.v6.
  rewrite !state_r1208_nr_5F1208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1208_nr_5F1208 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27609 (s : N.State) (i : N.Inputs) :
  R.v27609 (state s) (inputs i) = Zmod.unsigned (N.v27609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27609 s i)) at 1.
  unfold R.v27609, N.v27609.
  rewrite ?node_27607.
  rewrite ?node_27608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27610 (s : N.State) (i : N.Inputs) :
  R.v27610 (state s) (inputs i) = Zmod.unsigned (N.v27610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27610 s i)) at 1.
  unfold R.v27610, N.v27610.
  unfold R.v16484, N.v16484.
  rewrite ?node_27609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27611 (s : N.State) (i : N.Inputs) :
  R.v27611 (state s) (inputs i) = Zmod.unsigned (N.v27611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27611 s i)) at 1.
  unfold R.v27611, N.v27611.
  rewrite ?node_27606.
  rewrite ?node_27610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27612 (s : N.State) (i : N.Inputs) :
  R.v27612 (state s) (inputs i) = Zmod.unsigned (N.v27612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27612 s i)) at 1.
  unfold R.v27612, N.v27612.
  unfold R.v6, N.v6.
  rewrite ?node_27611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27613 (s : N.State) (i : N.Inputs) :
  R.v27613 (state s) (inputs i) = Zmod.unsigned (N.v27613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27613 s i)) at 1.
  unfold R.v27613, N.v27613.
  rewrite ?node_10642.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27614 (s : N.State) (i : N.Inputs) :
  R.v27614 (state s) (inputs i) = Zmod.unsigned (N.v27614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27614 s i)) at 1.
  unfold R.v27614, N.v27614.
  unfold R.v6, N.v6.
  rewrite ?node_10807.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27615 (s : N.State) (i : N.Inputs) :
  R.v27615 (state s) (inputs i) = Zmod.unsigned (N.v27615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27615 s i)) at 1.
  unfold R.v27615, N.v27615.
  rewrite ?node_27613.
  rewrite ?node_27614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27616 (s : N.State) (i : N.Inputs) :
  R.v27616 (state s) (inputs i) = Zmod.unsigned (N.v27616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27616 s i)) at 1.
  unfold R.v27616, N.v27616.
  rewrite ?node_27612.
  rewrite ?node_27615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27617 (s : N.State) (i : N.Inputs) :
  R.v27617 (state s) (inputs i) = Zmod.unsigned (N.v27617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27617 s i)) at 1.
  unfold R.v27617, N.v27617.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27618 (s : N.State) (i : N.Inputs) :
  R.v27618 (state s) (inputs i) = Zmod.unsigned (N.v27618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27618 s i)) at 1.
  unfold R.v27618, N.v27618.
  rewrite ?node_10646.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27619 (s : N.State) (i : N.Inputs) :
  R.v27619 (state s) (inputs i) = Zmod.unsigned (N.v27619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27619 s i)) at 1.
  unfold R.v27619, N.v27619.
  unfold R.v6, N.v6.
  rewrite !state_r1211_nr_5F1211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1211_nr_5F1211 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27620 (s : N.State) (i : N.Inputs) :
  R.v27620 (state s) (inputs i) = Zmod.unsigned (N.v27620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27620 s i)) at 1.
  unfold R.v27620, N.v27620.
  unfold R.v6, N.v6.
  rewrite ?node_10642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27621 (s : N.State) (i : N.Inputs) :
  R.v27621 (state s) (inputs i) = Zmod.unsigned (N.v27621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27621 s i)) at 1.
  unfold R.v27621, N.v27621.
  rewrite ?node_27619.
  rewrite ?node_27620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27622 (s : N.State) (i : N.Inputs) :
  R.v27622 (state s) (inputs i) = Zmod.unsigned (N.v27622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27622 s i)) at 1.
  unfold R.v27622, N.v27622.
  unfold R.v16484, N.v16484.
  rewrite ?node_27621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27623 (s : N.State) (i : N.Inputs) :
  R.v27623 (state s) (inputs i) = Zmod.unsigned (N.v27623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27623 s i)) at 1.
  unfold R.v27623, N.v27623.
  rewrite ?node_27618.
  rewrite ?node_27622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27624 (s : N.State) (i : N.Inputs) :
  R.v27624 (state s) (inputs i) = Zmod.unsigned (N.v27624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27624 s i)) at 1.
  unfold R.v27624, N.v27624.
  unfold R.v6, N.v6.
  rewrite ?node_27623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27625 (s : N.State) (i : N.Inputs) :
  R.v27625 (state s) (inputs i) = Zmod.unsigned (N.v27625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27625 s i)) at 1.
  unfold R.v27625, N.v27625.
  rewrite ?node_10647.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27626 (s : N.State) (i : N.Inputs) :
  R.v27626 (state s) (inputs i) = Zmod.unsigned (N.v27626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27626 s i)) at 1.
  unfold R.v27626, N.v27626.
  unfold R.v6, N.v6.
  rewrite ?node_10857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27627 (s : N.State) (i : N.Inputs) :
  R.v27627 (state s) (inputs i) = Zmod.unsigned (N.v27627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27627 s i)) at 1.
  unfold R.v27627, N.v27627.
  rewrite ?node_27625.
  rewrite ?node_27626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27628 (s : N.State) (i : N.Inputs) :
  R.v27628 (state s) (inputs i) = Zmod.unsigned (N.v27628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27628 s i)) at 1.
  unfold R.v27628, N.v27628.
  rewrite ?node_27624.
  rewrite ?node_27627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27629 (s : N.State) (i : N.Inputs) :
  R.v27629 (state s) (inputs i) = Zmod.unsigned (N.v27629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27629 s i)) at 1.
  unfold R.v27629, N.v27629.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27630 (s : N.State) (i : N.Inputs) :
  R.v27630 (state s) (inputs i) = Zmod.unsigned (N.v27630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27630 s i)) at 1.
  unfold R.v27630, N.v27630.
  rewrite ?node_10654.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27631 (s : N.State) (i : N.Inputs) :
  R.v27631 (state s) (inputs i) = Zmod.unsigned (N.v27631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27631 s i)) at 1.
  unfold R.v27631, N.v27631.
  unfold R.v16463, N.v16463.
  rewrite !state_r1215_nr_5F1215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1215_nr_5F1215 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27632 (s : N.State) (i : N.Inputs) :
  R.v27632 (state s) (inputs i) = Zmod.unsigned (N.v27632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27632 s i)) at 1.
  unfold R.v27632, N.v27632.
  unfold R.v16463, N.v16463.
  rewrite !state_r1214_nr_5F1214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1214_nr_5F1214 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27633 (s : N.State) (i : N.Inputs) :
  R.v27633 (state s) (inputs i) = Zmod.unsigned (N.v27633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27633 s i)) at 1.
  unfold R.v27633, N.v27633.
  unfold R.v6, N.v6.
  rewrite !state_r1213_nr_5F1213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1213_nr_5F1213 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27634 (s : N.State) (i : N.Inputs) :
  R.v27634 (state s) (inputs i) = Zmod.unsigned (N.v27634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27634 s i)) at 1.
  unfold R.v27634, N.v27634.
  unfold R.v6, N.v6.
  rewrite !state_r1212_nr_5F1212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1212_nr_5F1212 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27635 (s : N.State) (i : N.Inputs) :
  R.v27635 (state s) (inputs i) = Zmod.unsigned (N.v27635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27635 s i)) at 1.
  unfold R.v27635, N.v27635.
  rewrite ?node_27633.
  rewrite ?node_27634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27636 (s : N.State) (i : N.Inputs) :
  R.v27636 (state s) (inputs i) = Zmod.unsigned (N.v27636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27636 s i)) at 1.
  unfold R.v27636, N.v27636.
  unfold R.v16484, N.v16484.
  rewrite ?node_27635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27637 (s : N.State) (i : N.Inputs) :
  R.v27637 (state s) (inputs i) = Zmod.unsigned (N.v27637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27637 s i)) at 1.
  unfold R.v27637, N.v27637.
  rewrite ?node_27630.
  rewrite ?node_27631.
  rewrite ?node_27632.
  rewrite ?node_27636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27638 (s : N.State) (i : N.Inputs) :
  R.v27638 (state s) (inputs i) = Zmod.unsigned (N.v27638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27638 s i)) at 1.
  unfold R.v27638, N.v27638.
  unfold R.v6, N.v6.
  rewrite ?node_27637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27639 (s : N.State) (i : N.Inputs) :
  R.v27639 (state s) (inputs i) = Zmod.unsigned (N.v27639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27639 s i)) at 1.
  unfold R.v27639, N.v27639.
  rewrite ?node_10655.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27640 (s : N.State) (i : N.Inputs) :
  R.v27640 (state s) (inputs i) = Zmod.unsigned (N.v27640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27640 s i)) at 1.
  unfold R.v27640, N.v27640.
  unfold R.v6, N.v6.
  rewrite ?node_10815.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27641 (s : N.State) (i : N.Inputs) :
  R.v27641 (state s) (inputs i) = Zmod.unsigned (N.v27641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27641 s i)) at 1.
  unfold R.v27641, N.v27641.
  unfold R.v6, N.v6.
  rewrite ?node_10861.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27642 (s : N.State) (i : N.Inputs) :
  R.v27642 (state s) (inputs i) = Zmod.unsigned (N.v27642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27642 s i)) at 1.
  unfold R.v27642, N.v27642.
  rewrite ?node_27639.
  rewrite ?node_27640.
  rewrite ?node_27641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27643 (s : N.State) (i : N.Inputs) :
  R.v27643 (state s) (inputs i) = Zmod.unsigned (N.v27643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27643 s i)) at 1.
  unfold R.v27643, N.v27643.
  rewrite ?node_27638.
  rewrite ?node_27642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27644 (s : N.State) (i : N.Inputs) :
  R.v27644 (state s) (inputs i) = Zmod.unsigned (N.v27644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27644 s i)) at 1.
  unfold R.v27644, N.v27644.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27645 (s : N.State) (i : N.Inputs) :
  R.v27645 (state s) (inputs i) = Zmod.unsigned (N.v27645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27645 s i)) at 1.
  unfold R.v27645, N.v27645.
  unfold R.v16463, N.v16463.
  rewrite !state_r1214_nr_5F1214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1214_nr_5F1214 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27646 (s : N.State) (i : N.Inputs) :
  R.v27646 (state s) (inputs i) = Zmod.unsigned (N.v27646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27646 s i)) at 1.
  unfold R.v27646, N.v27646.
  unfold R.v6, N.v6.
  rewrite !state_r1213_nr_5F1213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1213_nr_5F1213 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27647 (s : N.State) (i : N.Inputs) :
  R.v27647 (state s) (inputs i) = Zmod.unsigned (N.v27647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27647 s i)) at 1.
  unfold R.v27647, N.v27647.
  unfold R.v6, N.v6.
  rewrite !state_r1212_nr_5F1212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1212_nr_5F1212 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27648 (s : N.State) (i : N.Inputs) :
  R.v27648 (state s) (inputs i) = Zmod.unsigned (N.v27648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27648 s i)) at 1.
  unfold R.v27648, N.v27648.
  rewrite ?node_27646.
  rewrite ?node_27647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27649 (s : N.State) (i : N.Inputs) :
  R.v27649 (state s) (inputs i) = Zmod.unsigned (N.v27649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27649 s i)) at 1.
  unfold R.v27649, N.v27649.
  unfold R.v16484, N.v16484.
  rewrite ?node_27648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27650 (s : N.State) (i : N.Inputs) :
  R.v27650 (state s) (inputs i) = Zmod.unsigned (N.v27650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27650 s i)) at 1.
  unfold R.v27650, N.v27650.
  rewrite ?node_27645.
  rewrite ?node_27649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27651 (s : N.State) (i : N.Inputs) :
  R.v27651 (state s) (inputs i) = Zmod.unsigned (N.v27651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27651 s i)) at 1.
  unfold R.v27651, N.v27651.
  unfold R.v6, N.v6.
  rewrite ?node_27650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27652 (s : N.State) (i : N.Inputs) :
  R.v27652 (state s) (inputs i) = Zmod.unsigned (N.v27652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27652 s i)) at 1.
  unfold R.v27652, N.v27652.
  rewrite ?node_10650.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27653 (s : N.State) (i : N.Inputs) :
  R.v27653 (state s) (inputs i) = Zmod.unsigned (N.v27653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27653 s i)) at 1.
  unfold R.v27653, N.v27653.
  unfold R.v6, N.v6.
  rewrite ?node_10815.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27654 (s : N.State) (i : N.Inputs) :
  R.v27654 (state s) (inputs i) = Zmod.unsigned (N.v27654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27654 s i)) at 1.
  unfold R.v27654, N.v27654.
  rewrite ?node_27652.
  rewrite ?node_27653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27655 (s : N.State) (i : N.Inputs) :
  R.v27655 (state s) (inputs i) = Zmod.unsigned (N.v27655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27655 s i)) at 1.
  unfold R.v27655, N.v27655.
  rewrite ?node_27651.
  rewrite ?node_27654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27656 (s : N.State) (i : N.Inputs) :
  R.v27656 (state s) (inputs i) = Zmod.unsigned (N.v27656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27656 s i)) at 1.
  unfold R.v27656, N.v27656.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27657 (s : N.State) (i : N.Inputs) :
  R.v27657 (state s) (inputs i) = Zmod.unsigned (N.v27657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27657 s i)) at 1.
  unfold R.v27657, N.v27657.
  rewrite ?node_10654.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27658 (s : N.State) (i : N.Inputs) :
  R.v27658 (state s) (inputs i) = Zmod.unsigned (N.v27658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27658 s i)) at 1.
  unfold R.v27658, N.v27658.
  unfold R.v6, N.v6.
  rewrite !state_r1215_nr_5F1215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1215_nr_5F1215 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27659 (s : N.State) (i : N.Inputs) :
  R.v27659 (state s) (inputs i) = Zmod.unsigned (N.v27659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27659 s i)) at 1.
  unfold R.v27659, N.v27659.
  unfold R.v6, N.v6.
  rewrite ?node_10650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27660 (s : N.State) (i : N.Inputs) :
  R.v27660 (state s) (inputs i) = Zmod.unsigned (N.v27660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27660 s i)) at 1.
  unfold R.v27660, N.v27660.
  rewrite ?node_27658.
  rewrite ?node_27659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27661 (s : N.State) (i : N.Inputs) :
  R.v27661 (state s) (inputs i) = Zmod.unsigned (N.v27661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27661 s i)) at 1.
  unfold R.v27661, N.v27661.
  unfold R.v16484, N.v16484.
  rewrite ?node_27660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27662 (s : N.State) (i : N.Inputs) :
  R.v27662 (state s) (inputs i) = Zmod.unsigned (N.v27662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27662 s i)) at 1.
  unfold R.v27662, N.v27662.
  rewrite ?node_27657.
  rewrite ?node_27661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27663 (s : N.State) (i : N.Inputs) :
  R.v27663 (state s) (inputs i) = Zmod.unsigned (N.v27663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27663 s i)) at 1.
  unfold R.v27663, N.v27663.
  unfold R.v6, N.v6.
  rewrite ?node_27662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27664 (s : N.State) (i : N.Inputs) :
  R.v27664 (state s) (inputs i) = Zmod.unsigned (N.v27664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27664 s i)) at 1.
  unfold R.v27664, N.v27664.
  rewrite ?node_10655.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27665 (s : N.State) (i : N.Inputs) :
  R.v27665 (state s) (inputs i) = Zmod.unsigned (N.v27665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27665 s i)) at 1.
  unfold R.v27665, N.v27665.
  unfold R.v6, N.v6.
  rewrite ?node_10861.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27666 (s : N.State) (i : N.Inputs) :
  R.v27666 (state s) (inputs i) = Zmod.unsigned (N.v27666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27666 s i)) at 1.
  unfold R.v27666, N.v27666.
  rewrite ?node_27664.
  rewrite ?node_27665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27667 (s : N.State) (i : N.Inputs) :
  R.v27667 (state s) (inputs i) = Zmod.unsigned (N.v27667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27667 s i)) at 1.
  unfold R.v27667, N.v27667.
  rewrite ?node_27663.
  rewrite ?node_27666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27668 (s : N.State) (i : N.Inputs) :
  R.v27668 (state s) (inputs i) = Zmod.unsigned (N.v27668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27668 s i)) at 1.
  unfold R.v27668, N.v27668.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27669 (s : N.State) (i : N.Inputs) :
  R.v27669 (state s) (inputs i) = Zmod.unsigned (N.v27669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27669 s i)) at 1.
  unfold R.v27669, N.v27669.
  rewrite ?node_10662.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27670 (s : N.State) (i : N.Inputs) :
  R.v27670 (state s) (inputs i) = Zmod.unsigned (N.v27670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27670 s i)) at 1.
  unfold R.v27670, N.v27670.
  unfold R.v16463, N.v16463.
  rewrite !state_r1219_nr_5F1219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1219_nr_5F1219 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27671 (s : N.State) (i : N.Inputs) :
  R.v27671 (state s) (inputs i) = Zmod.unsigned (N.v27671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27671 s i)) at 1.
  unfold R.v27671, N.v27671.
  unfold R.v16463, N.v16463.
  rewrite !state_r1218_nr_5F1218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1218_nr_5F1218 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27672 (s : N.State) (i : N.Inputs) :
  R.v27672 (state s) (inputs i) = Zmod.unsigned (N.v27672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27672 s i)) at 1.
  unfold R.v27672, N.v27672.
  unfold R.v6, N.v6.
  rewrite !state_r1217_nr_5F1217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1217_nr_5F1217 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27673 (s : N.State) (i : N.Inputs) :
  R.v27673 (state s) (inputs i) = Zmod.unsigned (N.v27673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27673 s i)) at 1.
  unfold R.v27673, N.v27673.
  unfold R.v6, N.v6.
  rewrite !state_r1216_nr_5F1216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1216_nr_5F1216 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27674 (s : N.State) (i : N.Inputs) :
  R.v27674 (state s) (inputs i) = Zmod.unsigned (N.v27674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27674 s i)) at 1.
  unfold R.v27674, N.v27674.
  rewrite ?node_27672.
  rewrite ?node_27673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27675 (s : N.State) (i : N.Inputs) :
  R.v27675 (state s) (inputs i) = Zmod.unsigned (N.v27675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27675 s i)) at 1.
  unfold R.v27675, N.v27675.
  unfold R.v16484, N.v16484.
  rewrite ?node_27674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27676 (s : N.State) (i : N.Inputs) :
  R.v27676 (state s) (inputs i) = Zmod.unsigned (N.v27676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27676 s i)) at 1.
  unfold R.v27676, N.v27676.
  rewrite ?node_27669.
  rewrite ?node_27670.
  rewrite ?node_27671.
  rewrite ?node_27675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27677 (s : N.State) (i : N.Inputs) :
  R.v27677 (state s) (inputs i) = Zmod.unsigned (N.v27677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27677 s i)) at 1.
  unfold R.v27677, N.v27677.
  unfold R.v6, N.v6.
  rewrite ?node_27676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27678 (s : N.State) (i : N.Inputs) :
  R.v27678 (state s) (inputs i) = Zmod.unsigned (N.v27678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27678 s i)) at 1.
  unfold R.v27678, N.v27678.
  rewrite ?node_10663.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27679 (s : N.State) (i : N.Inputs) :
  R.v27679 (state s) (inputs i) = Zmod.unsigned (N.v27679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27679 s i)) at 1.
  unfold R.v27679, N.v27679.
  unfold R.v6, N.v6.
  rewrite ?node_10823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27680 (s : N.State) (i : N.Inputs) :
  R.v27680 (state s) (inputs i) = Zmod.unsigned (N.v27680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27680 s i)) at 1.
  unfold R.v27680, N.v27680.
  unfold R.v6, N.v6.
  rewrite ?node_10874.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27681 (s : N.State) (i : N.Inputs) :
  R.v27681 (state s) (inputs i) = Zmod.unsigned (N.v27681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27681 s i)) at 1.
  unfold R.v27681, N.v27681.
  rewrite ?node_27678.
  rewrite ?node_27679.
  rewrite ?node_27680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27682 (s : N.State) (i : N.Inputs) :
  R.v27682 (state s) (inputs i) = Zmod.unsigned (N.v27682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27682 s i)) at 1.
  unfold R.v27682, N.v27682.
  rewrite ?node_27677.
  rewrite ?node_27681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27683 (s : N.State) (i : N.Inputs) :
  R.v27683 (state s) (inputs i) = Zmod.unsigned (N.v27683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27683 s i)) at 1.
  unfold R.v27683, N.v27683.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27684 (s : N.State) (i : N.Inputs) :
  R.v27684 (state s) (inputs i) = Zmod.unsigned (N.v27684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27684 s i)) at 1.
  unfold R.v27684, N.v27684.
  unfold R.v16463, N.v16463.
  rewrite !state_r1218_nr_5F1218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1218_nr_5F1218 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27685 (s : N.State) (i : N.Inputs) :
  R.v27685 (state s) (inputs i) = Zmod.unsigned (N.v27685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27685 s i)) at 1.
  unfold R.v27685, N.v27685.
  unfold R.v6, N.v6.
  rewrite !state_r1217_nr_5F1217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1217_nr_5F1217 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27686 (s : N.State) (i : N.Inputs) :
  R.v27686 (state s) (inputs i) = Zmod.unsigned (N.v27686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27686 s i)) at 1.
  unfold R.v27686, N.v27686.
  unfold R.v6, N.v6.
  rewrite !state_r1216_nr_5F1216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1216_nr_5F1216 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27687 (s : N.State) (i : N.Inputs) :
  R.v27687 (state s) (inputs i) = Zmod.unsigned (N.v27687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27687 s i)) at 1.
  unfold R.v27687, N.v27687.
  rewrite ?node_27685.
  rewrite ?node_27686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27688 (s : N.State) (i : N.Inputs) :
  R.v27688 (state s) (inputs i) = Zmod.unsigned (N.v27688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27688 s i)) at 1.
  unfold R.v27688, N.v27688.
  unfold R.v16484, N.v16484.
  rewrite ?node_27687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27689 (s : N.State) (i : N.Inputs) :
  R.v27689 (state s) (inputs i) = Zmod.unsigned (N.v27689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27689 s i)) at 1.
  unfold R.v27689, N.v27689.
  rewrite ?node_27684.
  rewrite ?node_27688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27690 (s : N.State) (i : N.Inputs) :
  R.v27690 (state s) (inputs i) = Zmod.unsigned (N.v27690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27690 s i)) at 1.
  unfold R.v27690, N.v27690.
  unfold R.v6, N.v6.
  rewrite ?node_27689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27691 (s : N.State) (i : N.Inputs) :
  R.v27691 (state s) (inputs i) = Zmod.unsigned (N.v27691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27691 s i)) at 1.
  unfold R.v27691, N.v27691.
  rewrite ?node_10658.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27692 (s : N.State) (i : N.Inputs) :
  R.v27692 (state s) (inputs i) = Zmod.unsigned (N.v27692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27692 s i)) at 1.
  unfold R.v27692, N.v27692.
  unfold R.v6, N.v6.
  rewrite ?node_10823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27693 (s : N.State) (i : N.Inputs) :
  R.v27693 (state s) (inputs i) = Zmod.unsigned (N.v27693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27693 s i)) at 1.
  unfold R.v27693, N.v27693.
  rewrite ?node_27691.
  rewrite ?node_27692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27694 (s : N.State) (i : N.Inputs) :
  R.v27694 (state s) (inputs i) = Zmod.unsigned (N.v27694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27694 s i)) at 1.
  unfold R.v27694, N.v27694.
  rewrite ?node_27690.
  rewrite ?node_27693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27695 (s : N.State) (i : N.Inputs) :
  R.v27695 (state s) (inputs i) = Zmod.unsigned (N.v27695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27695 s i)) at 1.
  unfold R.v27695, N.v27695.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27696 (s : N.State) (i : N.Inputs) :
  R.v27696 (state s) (inputs i) = Zmod.unsigned (N.v27696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27696 s i)) at 1.
  unfold R.v27696, N.v27696.
  rewrite ?node_10662.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27697 (s : N.State) (i : N.Inputs) :
  R.v27697 (state s) (inputs i) = Zmod.unsigned (N.v27697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27697 s i)) at 1.
  unfold R.v27697, N.v27697.
  unfold R.v6, N.v6.
  rewrite !state_r1219_nr_5F1219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1219_nr_5F1219 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27698 (s : N.State) (i : N.Inputs) :
  R.v27698 (state s) (inputs i) = Zmod.unsigned (N.v27698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27698 s i)) at 1.
  unfold R.v27698, N.v27698.
  unfold R.v6, N.v6.
  rewrite ?node_10658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27699 (s : N.State) (i : N.Inputs) :
  R.v27699 (state s) (inputs i) = Zmod.unsigned (N.v27699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27699 s i)) at 1.
  unfold R.v27699, N.v27699.
  rewrite ?node_27697.
  rewrite ?node_27698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27700 (s : N.State) (i : N.Inputs) :
  R.v27700 (state s) (inputs i) = Zmod.unsigned (N.v27700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27700 s i)) at 1.
  unfold R.v27700, N.v27700.
  unfold R.v16484, N.v16484.
  rewrite ?node_27699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27701 (s : N.State) (i : N.Inputs) :
  R.v27701 (state s) (inputs i) = Zmod.unsigned (N.v27701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27701 s i)) at 1.
  unfold R.v27701, N.v27701.
  rewrite ?node_27696.
  rewrite ?node_27700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27702 (s : N.State) (i : N.Inputs) :
  R.v27702 (state s) (inputs i) = Zmod.unsigned (N.v27702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27702 s i)) at 1.
  unfold R.v27702, N.v27702.
  unfold R.v6, N.v6.
  rewrite ?node_27701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27703 (s : N.State) (i : N.Inputs) :
  R.v27703 (state s) (inputs i) = Zmod.unsigned (N.v27703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27703 s i)) at 1.
  unfold R.v27703, N.v27703.
  rewrite ?node_10663.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27704 (s : N.State) (i : N.Inputs) :
  R.v27704 (state s) (inputs i) = Zmod.unsigned (N.v27704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27704 s i)) at 1.
  unfold R.v27704, N.v27704.
  unfold R.v6, N.v6.
  rewrite ?node_10874.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27705 (s : N.State) (i : N.Inputs) :
  R.v27705 (state s) (inputs i) = Zmod.unsigned (N.v27705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27705 s i)) at 1.
  unfold R.v27705, N.v27705.
  rewrite ?node_27703.
  rewrite ?node_27704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27706 (s : N.State) (i : N.Inputs) :
  R.v27706 (state s) (inputs i) = Zmod.unsigned (N.v27706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27706 s i)) at 1.
  unfold R.v27706, N.v27706.
  rewrite ?node_27702.
  rewrite ?node_27705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27707 (s : N.State) (i : N.Inputs) :
  R.v27707 (state s) (inputs i) = Zmod.unsigned (N.v27707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27707 s i)) at 1.
  unfold R.v27707, N.v27707.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27708 (s : N.State) (i : N.Inputs) :
  R.v27708 (state s) (inputs i) = Zmod.unsigned (N.v27708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27708 s i)) at 1.
  unfold R.v27708, N.v27708.
  rewrite ?node_10765.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27709 (s : N.State) (i : N.Inputs) :
  R.v27709 (state s) (inputs i) = Zmod.unsigned (N.v27709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27709 s i)) at 1.
  unfold R.v27709, N.v27709.
  unfold R.v16463, N.v16463.
  rewrite !state_r1224_nr_5F1224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1224_nr_5F1224 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27710 (s : N.State) (i : N.Inputs) :
  R.v27710 (state s) (inputs i) = Zmod.unsigned (N.v27710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27710 s i)) at 1.
  unfold R.v27710, N.v27710.
  unfold R.v16463, N.v16463.
  rewrite !state_r1223_nr_5F1223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1223_nr_5F1223 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27711 (s : N.State) (i : N.Inputs) :
  R.v27711 (state s) (inputs i) = Zmod.unsigned (N.v27711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27711 s i)) at 1.
  unfold R.v27711, N.v27711.
  unfold R.v6, N.v6.
  rewrite !state_r1222_nr_5F1222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1222_nr_5F1222 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27712 (s : N.State) (i : N.Inputs) :
  R.v27712 (state s) (inputs i) = Zmod.unsigned (N.v27712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27712 s i)) at 1.
  unfold R.v27712, N.v27712.
  unfold R.v6, N.v6.
  rewrite !state_r1221_nr_5F1221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1221_nr_5F1221 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27713 (s : N.State) (i : N.Inputs) :
  R.v27713 (state s) (inputs i) = Zmod.unsigned (N.v27713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27713 s i)) at 1.
  unfold R.v27713, N.v27713.
  rewrite ?node_27711.
  rewrite ?node_27712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27714 (s : N.State) (i : N.Inputs) :
  R.v27714 (state s) (inputs i) = Zmod.unsigned (N.v27714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27714 s i)) at 1.
  unfold R.v27714, N.v27714.
  unfold R.v16484, N.v16484.
  rewrite ?node_27713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27715 (s : N.State) (i : N.Inputs) :
  R.v27715 (state s) (inputs i) = Zmod.unsigned (N.v27715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27715 s i)) at 1.
  unfold R.v27715, N.v27715.
  rewrite ?node_27708.
  rewrite ?node_27709.
  rewrite ?node_27710.
  rewrite ?node_27714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27716 (s : N.State) (i : N.Inputs) :
  R.v27716 (state s) (inputs i) = Zmod.unsigned (N.v27716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27716 s i)) at 1.
  unfold R.v27716, N.v27716.
  unfold R.v6, N.v6.
  rewrite ?node_27715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27717 (s : N.State) (i : N.Inputs) :
  R.v27717 (state s) (inputs i) = Zmod.unsigned (N.v27717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27717 s i)) at 1.
  unfold R.v27717, N.v27717.
  rewrite ?node_10766.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27718 (s : N.State) (i : N.Inputs) :
  R.v27718 (state s) (inputs i) = Zmod.unsigned (N.v27718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27718 s i)) at 1.
  unfold R.v27718, N.v27718.
  unfold R.v6, N.v6.
  rewrite ?node_10926.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27719 (s : N.State) (i : N.Inputs) :
  R.v27719 (state s) (inputs i) = Zmod.unsigned (N.v27719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27719 s i)) at 1.
  unfold R.v27719, N.v27719.
  unfold R.v6, N.v6.
  rewrite ?node_10994.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27720 (s : N.State) (i : N.Inputs) :
  R.v27720 (state s) (inputs i) = Zmod.unsigned (N.v27720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27720 s i)) at 1.
  unfold R.v27720, N.v27720.
  rewrite ?node_27717.
  rewrite ?node_27718.
  rewrite ?node_27719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27721 (s : N.State) (i : N.Inputs) :
  R.v27721 (state s) (inputs i) = Zmod.unsigned (N.v27721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27721 s i)) at 1.
  unfold R.v27721, N.v27721.
  rewrite ?node_27716.
  rewrite ?node_27720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27722 (s : N.State) (i : N.Inputs) :
  R.v27722 (state s) (inputs i) = Zmod.unsigned (N.v27722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27722 s i)) at 1.
  unfold R.v27722, N.v27722.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27723 (s : N.State) (i : N.Inputs) :
  R.v27723 (state s) (inputs i) = Zmod.unsigned (N.v27723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27723 s i)) at 1.
  unfold R.v27723, N.v27723.
  unfold R.v16463, N.v16463.
  rewrite !state_r1223_nr_5F1223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1223_nr_5F1223 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27724 (s : N.State) (i : N.Inputs) :
  R.v27724 (state s) (inputs i) = Zmod.unsigned (N.v27724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27724 s i)) at 1.
  unfold R.v27724, N.v27724.
  unfold R.v6, N.v6.
  rewrite !state_r1222_nr_5F1222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1222_nr_5F1222 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27725 (s : N.State) (i : N.Inputs) :
  R.v27725 (state s) (inputs i) = Zmod.unsigned (N.v27725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27725 s i)) at 1.
  unfold R.v27725, N.v27725.
  unfold R.v6, N.v6.
  rewrite !state_r1221_nr_5F1221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1221_nr_5F1221 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27726 (s : N.State) (i : N.Inputs) :
  R.v27726 (state s) (inputs i) = Zmod.unsigned (N.v27726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27726 s i)) at 1.
  unfold R.v27726, N.v27726.
  rewrite ?node_27724.
  rewrite ?node_27725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27727 (s : N.State) (i : N.Inputs) :
  R.v27727 (state s) (inputs i) = Zmod.unsigned (N.v27727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27727 s i)) at 1.
  unfold R.v27727, N.v27727.
  unfold R.v16484, N.v16484.
  rewrite ?node_27726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27728 (s : N.State) (i : N.Inputs) :
  R.v27728 (state s) (inputs i) = Zmod.unsigned (N.v27728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27728 s i)) at 1.
  unfold R.v27728, N.v27728.
  rewrite ?node_27723.
  rewrite ?node_27727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27729 (s : N.State) (i : N.Inputs) :
  R.v27729 (state s) (inputs i) = Zmod.unsigned (N.v27729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27729 s i)) at 1.
  unfold R.v27729, N.v27729.
  unfold R.v6, N.v6.
  rewrite ?node_27728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27730 (s : N.State) (i : N.Inputs) :
  R.v27730 (state s) (inputs i) = Zmod.unsigned (N.v27730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27730 s i)) at 1.
  unfold R.v27730, N.v27730.
  rewrite ?node_10761.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27731 (s : N.State) (i : N.Inputs) :
  R.v27731 (state s) (inputs i) = Zmod.unsigned (N.v27731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27731 s i)) at 1.
  unfold R.v27731, N.v27731.
  unfold R.v6, N.v6.
  rewrite ?node_10926.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27732 (s : N.State) (i : N.Inputs) :
  R.v27732 (state s) (inputs i) = Zmod.unsigned (N.v27732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27732 s i)) at 1.
  unfold R.v27732, N.v27732.
  rewrite ?node_27730.
  rewrite ?node_27731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27733 (s : N.State) (i : N.Inputs) :
  R.v27733 (state s) (inputs i) = Zmod.unsigned (N.v27733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27733 s i)) at 1.
  unfold R.v27733, N.v27733.
  rewrite ?node_27729.
  rewrite ?node_27732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27734 (s : N.State) (i : N.Inputs) :
  R.v27734 (state s) (inputs i) = Zmod.unsigned (N.v27734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27734 s i)) at 1.
  unfold R.v27734, N.v27734.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27735 (s : N.State) (i : N.Inputs) :
  R.v27735 (state s) (inputs i) = Zmod.unsigned (N.v27735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27735 s i)) at 1.
  unfold R.v27735, N.v27735.
  rewrite ?node_10765.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27736 (s : N.State) (i : N.Inputs) :
  R.v27736 (state s) (inputs i) = Zmod.unsigned (N.v27736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27736 s i)) at 1.
  unfold R.v27736, N.v27736.
  unfold R.v6, N.v6.
  rewrite !state_r1224_nr_5F1224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1224_nr_5F1224 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27737 (s : N.State) (i : N.Inputs) :
  R.v27737 (state s) (inputs i) = Zmod.unsigned (N.v27737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27737 s i)) at 1.
  unfold R.v27737, N.v27737.
  unfold R.v6, N.v6.
  rewrite ?node_10761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27738 (s : N.State) (i : N.Inputs) :
  R.v27738 (state s) (inputs i) = Zmod.unsigned (N.v27738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27738 s i)) at 1.
  unfold R.v27738, N.v27738.
  rewrite ?node_27736.
  rewrite ?node_27737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27739 (s : N.State) (i : N.Inputs) :
  R.v27739 (state s) (inputs i) = Zmod.unsigned (N.v27739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27739 s i)) at 1.
  unfold R.v27739, N.v27739.
  unfold R.v16484, N.v16484.
  rewrite ?node_27738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27740 (s : N.State) (i : N.Inputs) :
  R.v27740 (state s) (inputs i) = Zmod.unsigned (N.v27740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27740 s i)) at 1.
  unfold R.v27740, N.v27740.
  rewrite ?node_27735.
  rewrite ?node_27739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27741 (s : N.State) (i : N.Inputs) :
  R.v27741 (state s) (inputs i) = Zmod.unsigned (N.v27741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27741 s i)) at 1.
  unfold R.v27741, N.v27741.
  unfold R.v6, N.v6.
  rewrite ?node_27740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27742 (s : N.State) (i : N.Inputs) :
  R.v27742 (state s) (inputs i) = Zmod.unsigned (N.v27742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27742 s i)) at 1.
  unfold R.v27742, N.v27742.
  rewrite ?node_10766.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27743 (s : N.State) (i : N.Inputs) :
  R.v27743 (state s) (inputs i) = Zmod.unsigned (N.v27743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27743 s i)) at 1.
  unfold R.v27743, N.v27743.
  unfold R.v6, N.v6.
  rewrite ?node_10994.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27744 (s : N.State) (i : N.Inputs) :
  R.v27744 (state s) (inputs i) = Zmod.unsigned (N.v27744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27744 s i)) at 1.
  unfold R.v27744, N.v27744.
  rewrite ?node_27742.
  rewrite ?node_27743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27745 (s : N.State) (i : N.Inputs) :
  R.v27745 (state s) (inputs i) = Zmod.unsigned (N.v27745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27745 s i)) at 1.
  unfold R.v27745, N.v27745.
  rewrite ?node_27741.
  rewrite ?node_27744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27746 (s : N.State) (i : N.Inputs) :
  R.v27746 (state s) (inputs i) = Zmod.unsigned (N.v27746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27746 s i)) at 1.
  unfold R.v27746, N.v27746.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27747 (s : N.State) (i : N.Inputs) :
  R.v27747 (state s) (inputs i) = Zmod.unsigned (N.v27747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27747 s i)) at 1.
  unfold R.v27747, N.v27747.
  rewrite ?node_10772.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27748 (s : N.State) (i : N.Inputs) :
  R.v27748 (state s) (inputs i) = Zmod.unsigned (N.v27748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27748 s i)) at 1.
  unfold R.v27748, N.v27748.
  unfold R.v16463, N.v16463.
  rewrite !state_r1228_nr_5F1228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1228_nr_5F1228 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27749 (s : N.State) (i : N.Inputs) :
  R.v27749 (state s) (inputs i) = Zmod.unsigned (N.v27749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27749 s i)) at 1.
  unfold R.v27749, N.v27749.
  unfold R.v16463, N.v16463.
  rewrite !state_r1227_nr_5F1227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1227_nr_5F1227 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27750 (s : N.State) (i : N.Inputs) :
  R.v27750 (state s) (inputs i) = Zmod.unsigned (N.v27750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27750 s i)) at 1.
  unfold R.v27750, N.v27750.
  unfold R.v6, N.v6.
  rewrite !state_r1226_nr_5F1226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1226_nr_5F1226 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27751 (s : N.State) (i : N.Inputs) :
  R.v27751 (state s) (inputs i) = Zmod.unsigned (N.v27751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27751 s i)) at 1.
  unfold R.v27751, N.v27751.
  unfold R.v6, N.v6.
  rewrite !state_r1225_nr_5F1225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1225_nr_5F1225 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27752 (s : N.State) (i : N.Inputs) :
  R.v27752 (state s) (inputs i) = Zmod.unsigned (N.v27752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27752 s i)) at 1.
  unfold R.v27752, N.v27752.
  rewrite ?node_27750.
  rewrite ?node_27751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27753 (s : N.State) (i : N.Inputs) :
  R.v27753 (state s) (inputs i) = Zmod.unsigned (N.v27753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27753 s i)) at 1.
  unfold R.v27753, N.v27753.
  unfold R.v16484, N.v16484.
  rewrite ?node_27752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27754 (s : N.State) (i : N.Inputs) :
  R.v27754 (state s) (inputs i) = Zmod.unsigned (N.v27754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27754 s i)) at 1.
  unfold R.v27754, N.v27754.
  rewrite ?node_27747.
  rewrite ?node_27748.
  rewrite ?node_27749.
  rewrite ?node_27753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27755 (s : N.State) (i : N.Inputs) :
  R.v27755 (state s) (inputs i) = Zmod.unsigned (N.v27755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27755 s i)) at 1.
  unfold R.v27755, N.v27755.
  unfold R.v6, N.v6.
  rewrite ?node_27754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27756 (s : N.State) (i : N.Inputs) :
  R.v27756 (state s) (inputs i) = Zmod.unsigned (N.v27756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27756 s i)) at 1.
  unfold R.v27756, N.v27756.
  rewrite ?node_10773.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27757 (s : N.State) (i : N.Inputs) :
  R.v27757 (state s) (inputs i) = Zmod.unsigned (N.v27757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27757 s i)) at 1.
  unfold R.v27757, N.v27757.
  unfold R.v6, N.v6.
  rewrite ?node_10933.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27758 (s : N.State) (i : N.Inputs) :
  R.v27758 (state s) (inputs i) = Zmod.unsigned (N.v27758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27758 s i)) at 1.
  unfold R.v27758, N.v27758.
  unfold R.v6, N.v6.
  rewrite ?node_10998.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27759 (s : N.State) (i : N.Inputs) :
  R.v27759 (state s) (inputs i) = Zmod.unsigned (N.v27759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27759 s i)) at 1.
  unfold R.v27759, N.v27759.
  rewrite ?node_27756.
  rewrite ?node_27757.
  rewrite ?node_27758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27760 (s : N.State) (i : N.Inputs) :
  R.v27760 (state s) (inputs i) = Zmod.unsigned (N.v27760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27760 s i)) at 1.
  unfold R.v27760, N.v27760.
  rewrite ?node_27755.
  rewrite ?node_27759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27761 (s : N.State) (i : N.Inputs) :
  R.v27761 (state s) (inputs i) = Zmod.unsigned (N.v27761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27761 s i)) at 1.
  unfold R.v27761, N.v27761.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27762 (s : N.State) (i : N.Inputs) :
  R.v27762 (state s) (inputs i) = Zmod.unsigned (N.v27762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27762 s i)) at 1.
  unfold R.v27762, N.v27762.
  unfold R.v16463, N.v16463.
  rewrite !state_r1227_nr_5F1227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1227_nr_5F1227 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27763 (s : N.State) (i : N.Inputs) :
  R.v27763 (state s) (inputs i) = Zmod.unsigned (N.v27763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27763 s i)) at 1.
  unfold R.v27763, N.v27763.
  unfold R.v6, N.v6.
  rewrite !state_r1226_nr_5F1226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1226_nr_5F1226 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27764 (s : N.State) (i : N.Inputs) :
  R.v27764 (state s) (inputs i) = Zmod.unsigned (N.v27764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27764 s i)) at 1.
  unfold R.v27764, N.v27764.
  unfold R.v6, N.v6.
  rewrite !state_r1225_nr_5F1225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1225_nr_5F1225 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27765 (s : N.State) (i : N.Inputs) :
  R.v27765 (state s) (inputs i) = Zmod.unsigned (N.v27765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27765 s i)) at 1.
  unfold R.v27765, N.v27765.
  rewrite ?node_27763.
  rewrite ?node_27764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27766 (s : N.State) (i : N.Inputs) :
  R.v27766 (state s) (inputs i) = Zmod.unsigned (N.v27766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27766 s i)) at 1.
  unfold R.v27766, N.v27766.
  unfold R.v16484, N.v16484.
  rewrite ?node_27765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27767 (s : N.State) (i : N.Inputs) :
  R.v27767 (state s) (inputs i) = Zmod.unsigned (N.v27767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27767 s i)) at 1.
  unfold R.v27767, N.v27767.
  rewrite ?node_27762.
  rewrite ?node_27766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27768 (s : N.State) (i : N.Inputs) :
  R.v27768 (state s) (inputs i) = Zmod.unsigned (N.v27768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27768 s i)) at 1.
  unfold R.v27768, N.v27768.
  unfold R.v6, N.v6.
  rewrite ?node_27767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27769 (s : N.State) (i : N.Inputs) :
  R.v27769 (state s) (inputs i) = Zmod.unsigned (N.v27769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27769 s i)) at 1.
  unfold R.v27769, N.v27769.
  rewrite ?node_10768.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27770 (s : N.State) (i : N.Inputs) :
  R.v27770 (state s) (inputs i) = Zmod.unsigned (N.v27770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27770 s i)) at 1.
  unfold R.v27770, N.v27770.
  unfold R.v6, N.v6.
  rewrite ?node_10933.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27771 (s : N.State) (i : N.Inputs) :
  R.v27771 (state s) (inputs i) = Zmod.unsigned (N.v27771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27771 s i)) at 1.
  unfold R.v27771, N.v27771.
  rewrite ?node_27769.
  rewrite ?node_27770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27772 (s : N.State) (i : N.Inputs) :
  R.v27772 (state s) (inputs i) = Zmod.unsigned (N.v27772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27772 s i)) at 1.
  unfold R.v27772, N.v27772.
  rewrite ?node_27768.
  rewrite ?node_27771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27773 (s : N.State) (i : N.Inputs) :
  R.v27773 (state s) (inputs i) = Zmod.unsigned (N.v27773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27773 s i)) at 1.
  unfold R.v27773, N.v27773.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27774 (s : N.State) (i : N.Inputs) :
  R.v27774 (state s) (inputs i) = Zmod.unsigned (N.v27774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27774 s i)) at 1.
  unfold R.v27774, N.v27774.
  rewrite ?node_10772.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27775 (s : N.State) (i : N.Inputs) :
  R.v27775 (state s) (inputs i) = Zmod.unsigned (N.v27775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27775 s i)) at 1.
  unfold R.v27775, N.v27775.
  unfold R.v6, N.v6.
  rewrite !state_r1228_nr_5F1228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1228_nr_5F1228 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27776 (s : N.State) (i : N.Inputs) :
  R.v27776 (state s) (inputs i) = Zmod.unsigned (N.v27776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27776 s i)) at 1.
  unfold R.v27776, N.v27776.
  unfold R.v6, N.v6.
  rewrite ?node_10768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27777 (s : N.State) (i : N.Inputs) :
  R.v27777 (state s) (inputs i) = Zmod.unsigned (N.v27777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27777 s i)) at 1.
  unfold R.v27777, N.v27777.
  rewrite ?node_27775.
  rewrite ?node_27776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27778 (s : N.State) (i : N.Inputs) :
  R.v27778 (state s) (inputs i) = Zmod.unsigned (N.v27778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27778 s i)) at 1.
  unfold R.v27778, N.v27778.
  unfold R.v16484, N.v16484.
  rewrite ?node_27777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27779 (s : N.State) (i : N.Inputs) :
  R.v27779 (state s) (inputs i) = Zmod.unsigned (N.v27779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27779 s i)) at 1.
  unfold R.v27779, N.v27779.
  rewrite ?node_27774.
  rewrite ?node_27778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27780 (s : N.State) (i : N.Inputs) :
  R.v27780 (state s) (inputs i) = Zmod.unsigned (N.v27780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27780 s i)) at 1.
  unfold R.v27780, N.v27780.
  unfold R.v6, N.v6.
  rewrite ?node_27779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27781 (s : N.State) (i : N.Inputs) :
  R.v27781 (state s) (inputs i) = Zmod.unsigned (N.v27781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27781 s i)) at 1.
  unfold R.v27781, N.v27781.
  rewrite ?node_10773.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27782 (s : N.State) (i : N.Inputs) :
  R.v27782 (state s) (inputs i) = Zmod.unsigned (N.v27782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27782 s i)) at 1.
  unfold R.v27782, N.v27782.
  unfold R.v6, N.v6.
  rewrite ?node_10998.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27783 (s : N.State) (i : N.Inputs) :
  R.v27783 (state s) (inputs i) = Zmod.unsigned (N.v27783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27783 s i)) at 1.
  unfold R.v27783, N.v27783.
  rewrite ?node_27781.
  rewrite ?node_27782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27784 (s : N.State) (i : N.Inputs) :
  R.v27784 (state s) (inputs i) = Zmod.unsigned (N.v27784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27784 s i)) at 1.
  unfold R.v27784, N.v27784.
  rewrite ?node_27780.
  rewrite ?node_27783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27785 (s : N.State) (i : N.Inputs) :
  R.v27785 (state s) (inputs i) = Zmod.unsigned (N.v27785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27785 s i)) at 1.
  unfold R.v27785, N.v27785.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27786 (s : N.State) (i : N.Inputs) :
  R.v27786 (state s) (inputs i) = Zmod.unsigned (N.v27786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27786 s i)) at 1.
  unfold R.v27786, N.v27786.
  rewrite ?node_10780.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27787 (s : N.State) (i : N.Inputs) :
  R.v27787 (state s) (inputs i) = Zmod.unsigned (N.v27787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27787 s i)) at 1.
  unfold R.v27787, N.v27787.
  unfold R.v16463, N.v16463.
  rewrite !state_r1232_nr_5F1232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1232_nr_5F1232 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27788 (s : N.State) (i : N.Inputs) :
  R.v27788 (state s) (inputs i) = Zmod.unsigned (N.v27788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27788 s i)) at 1.
  unfold R.v27788, N.v27788.
  unfold R.v16463, N.v16463.
  rewrite !state_r1231_nr_5F1231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1231_nr_5F1231 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27789 (s : N.State) (i : N.Inputs) :
  R.v27789 (state s) (inputs i) = Zmod.unsigned (N.v27789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27789 s i)) at 1.
  unfold R.v27789, N.v27789.
  unfold R.v6, N.v6.
  rewrite !state_r1230_nr_5F1230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1230_nr_5F1230 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27790 (s : N.State) (i : N.Inputs) :
  R.v27790 (state s) (inputs i) = Zmod.unsigned (N.v27790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27790 s i)) at 1.
  unfold R.v27790, N.v27790.
  unfold R.v6, N.v6.
  rewrite !state_r1229_nr_5F1229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1229_nr_5F1229 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27791 (s : N.State) (i : N.Inputs) :
  R.v27791 (state s) (inputs i) = Zmod.unsigned (N.v27791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27791 s i)) at 1.
  unfold R.v27791, N.v27791.
  rewrite ?node_27789.
  rewrite ?node_27790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27792 (s : N.State) (i : N.Inputs) :
  R.v27792 (state s) (inputs i) = Zmod.unsigned (N.v27792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27792 s i)) at 1.
  unfold R.v27792, N.v27792.
  unfold R.v16484, N.v16484.
  rewrite ?node_27791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27793 (s : N.State) (i : N.Inputs) :
  R.v27793 (state s) (inputs i) = Zmod.unsigned (N.v27793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27793 s i)) at 1.
  unfold R.v27793, N.v27793.
  rewrite ?node_27786.
  rewrite ?node_27787.
  rewrite ?node_27788.
  rewrite ?node_27792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27794 (s : N.State) (i : N.Inputs) :
  R.v27794 (state s) (inputs i) = Zmod.unsigned (N.v27794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27794 s i)) at 1.
  unfold R.v27794, N.v27794.
  unfold R.v6, N.v6.
  rewrite ?node_27793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27795 (s : N.State) (i : N.Inputs) :
  R.v27795 (state s) (inputs i) = Zmod.unsigned (N.v27795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27795 s i)) at 1.
  unfold R.v27795, N.v27795.
  rewrite ?node_10781.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27796 (s : N.State) (i : N.Inputs) :
  R.v27796 (state s) (inputs i) = Zmod.unsigned (N.v27796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27796 s i)) at 1.
  unfold R.v27796, N.v27796.
  unfold R.v6, N.v6.
  rewrite ?node_10941.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27797 (s : N.State) (i : N.Inputs) :
  R.v27797 (state s) (inputs i) = Zmod.unsigned (N.v27797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27797 s i)) at 1.
  unfold R.v27797, N.v27797.
  unfold R.v6, N.v6.
  rewrite ?node_11002.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27798 (s : N.State) (i : N.Inputs) :
  R.v27798 (state s) (inputs i) = Zmod.unsigned (N.v27798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27798 s i)) at 1.
  unfold R.v27798, N.v27798.
  rewrite ?node_27795.
  rewrite ?node_27796.
  rewrite ?node_27797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27799 (s : N.State) (i : N.Inputs) :
  R.v27799 (state s) (inputs i) = Zmod.unsigned (N.v27799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27799 s i)) at 1.
  unfold R.v27799, N.v27799.
  rewrite ?node_27794.
  rewrite ?node_27798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27800 (s : N.State) (i : N.Inputs) :
  R.v27800 (state s) (inputs i) = Zmod.unsigned (N.v27800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27800 s i)) at 1.
  unfold R.v27800, N.v27800.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27801 (s : N.State) (i : N.Inputs) :
  R.v27801 (state s) (inputs i) = Zmod.unsigned (N.v27801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27801 s i)) at 1.
  unfold R.v27801, N.v27801.
  unfold R.v16463, N.v16463.
  rewrite !state_r1231_nr_5F1231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1231_nr_5F1231 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27802 (s : N.State) (i : N.Inputs) :
  R.v27802 (state s) (inputs i) = Zmod.unsigned (N.v27802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27802 s i)) at 1.
  unfold R.v27802, N.v27802.
  unfold R.v6, N.v6.
  rewrite !state_r1230_nr_5F1230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1230_nr_5F1230 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27803 (s : N.State) (i : N.Inputs) :
  R.v27803 (state s) (inputs i) = Zmod.unsigned (N.v27803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27803 s i)) at 1.
  unfold R.v27803, N.v27803.
  unfold R.v6, N.v6.
  rewrite !state_r1229_nr_5F1229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1229_nr_5F1229 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27804 (s : N.State) (i : N.Inputs) :
  R.v27804 (state s) (inputs i) = Zmod.unsigned (N.v27804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27804 s i)) at 1.
  unfold R.v27804, N.v27804.
  rewrite ?node_27802.
  rewrite ?node_27803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27805 (s : N.State) (i : N.Inputs) :
  R.v27805 (state s) (inputs i) = Zmod.unsigned (N.v27805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27805 s i)) at 1.
  unfold R.v27805, N.v27805.
  unfold R.v16484, N.v16484.
  rewrite ?node_27804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27806 (s : N.State) (i : N.Inputs) :
  R.v27806 (state s) (inputs i) = Zmod.unsigned (N.v27806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27806 s i)) at 1.
  unfold R.v27806, N.v27806.
  rewrite ?node_27801.
  rewrite ?node_27805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27807 (s : N.State) (i : N.Inputs) :
  R.v27807 (state s) (inputs i) = Zmod.unsigned (N.v27807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27807 s i)) at 1.
  unfold R.v27807, N.v27807.
  unfold R.v6, N.v6.
  rewrite ?node_27806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27808 (s : N.State) (i : N.Inputs) :
  R.v27808 (state s) (inputs i) = Zmod.unsigned (N.v27808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27808 s i)) at 1.
  unfold R.v27808, N.v27808.
  rewrite ?node_10776.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27809 (s : N.State) (i : N.Inputs) :
  R.v27809 (state s) (inputs i) = Zmod.unsigned (N.v27809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27809 s i)) at 1.
  unfold R.v27809, N.v27809.
  unfold R.v6, N.v6.
  rewrite ?node_10941.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27810 (s : N.State) (i : N.Inputs) :
  R.v27810 (state s) (inputs i) = Zmod.unsigned (N.v27810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27810 s i)) at 1.
  unfold R.v27810, N.v27810.
  rewrite ?node_27808.
  rewrite ?node_27809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27811 (s : N.State) (i : N.Inputs) :
  R.v27811 (state s) (inputs i) = Zmod.unsigned (N.v27811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27811 s i)) at 1.
  unfold R.v27811, N.v27811.
  rewrite ?node_27807.
  rewrite ?node_27810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27812 (s : N.State) (i : N.Inputs) :
  R.v27812 (state s) (inputs i) = Zmod.unsigned (N.v27812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27812 s i)) at 1.
  unfold R.v27812, N.v27812.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27813 (s : N.State) (i : N.Inputs) :
  R.v27813 (state s) (inputs i) = Zmod.unsigned (N.v27813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27813 s i)) at 1.
  unfold R.v27813, N.v27813.
  rewrite ?node_10780.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27814 (s : N.State) (i : N.Inputs) :
  R.v27814 (state s) (inputs i) = Zmod.unsigned (N.v27814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27814 s i)) at 1.
  unfold R.v27814, N.v27814.
  unfold R.v6, N.v6.
  rewrite !state_r1232_nr_5F1232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1232_nr_5F1232 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27815 (s : N.State) (i : N.Inputs) :
  R.v27815 (state s) (inputs i) = Zmod.unsigned (N.v27815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27815 s i)) at 1.
  unfold R.v27815, N.v27815.
  unfold R.v6, N.v6.
  rewrite ?node_10776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27816 (s : N.State) (i : N.Inputs) :
  R.v27816 (state s) (inputs i) = Zmod.unsigned (N.v27816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27816 s i)) at 1.
  unfold R.v27816, N.v27816.
  rewrite ?node_27814.
  rewrite ?node_27815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27817 (s : N.State) (i : N.Inputs) :
  R.v27817 (state s) (inputs i) = Zmod.unsigned (N.v27817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27817 s i)) at 1.
  unfold R.v27817, N.v27817.
  unfold R.v16484, N.v16484.
  rewrite ?node_27816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27818 (s : N.State) (i : N.Inputs) :
  R.v27818 (state s) (inputs i) = Zmod.unsigned (N.v27818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27818 s i)) at 1.
  unfold R.v27818, N.v27818.
  rewrite ?node_27813.
  rewrite ?node_27817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27819 (s : N.State) (i : N.Inputs) :
  R.v27819 (state s) (inputs i) = Zmod.unsigned (N.v27819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27819 s i)) at 1.
  unfold R.v27819, N.v27819.
  unfold R.v6, N.v6.
  rewrite ?node_27818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27820 (s : N.State) (i : N.Inputs) :
  R.v27820 (state s) (inputs i) = Zmod.unsigned (N.v27820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27820 s i)) at 1.
  unfold R.v27820, N.v27820.
  rewrite ?node_10781.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27821 (s : N.State) (i : N.Inputs) :
  R.v27821 (state s) (inputs i) = Zmod.unsigned (N.v27821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27821 s i)) at 1.
  unfold R.v27821, N.v27821.
  unfold R.v6, N.v6.
  rewrite ?node_11002.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27822 (s : N.State) (i : N.Inputs) :
  R.v27822 (state s) (inputs i) = Zmod.unsigned (N.v27822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27822 s i)) at 1.
  unfold R.v27822, N.v27822.
  rewrite ?node_27820.
  rewrite ?node_27821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27823 (s : N.State) (i : N.Inputs) :
  R.v27823 (state s) (inputs i) = Zmod.unsigned (N.v27823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27823 s i)) at 1.
  unfold R.v27823, N.v27823.
  rewrite ?node_27819.
  rewrite ?node_27822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27824 (s : N.State) (i : N.Inputs) :
  R.v27824 (state s) (inputs i) = Zmod.unsigned (N.v27824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27824 s i)) at 1.
  unfold R.v27824, N.v27824.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27825 (s : N.State) (i : N.Inputs) :
  R.v27825 (state s) (inputs i) = Zmod.unsigned (N.v27825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27825 s i)) at 1.
  unfold R.v27825, N.v27825.
  rewrite ?node_10788.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27826 (s : N.State) (i : N.Inputs) :
  R.v27826 (state s) (inputs i) = Zmod.unsigned (N.v27826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27826 s i)) at 1.
  unfold R.v27826, N.v27826.
  unfold R.v16463, N.v16463.
  rewrite !state_r1236_nr_5F1236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1236_nr_5F1236 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27827 (s : N.State) (i : N.Inputs) :
  R.v27827 (state s) (inputs i) = Zmod.unsigned (N.v27827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27827 s i)) at 1.
  unfold R.v27827, N.v27827.
  unfold R.v16463, N.v16463.
  rewrite !state_r1235_nr_5F1235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1235_nr_5F1235 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27828 (s : N.State) (i : N.Inputs) :
  R.v27828 (state s) (inputs i) = Zmod.unsigned (N.v27828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27828 s i)) at 1.
  unfold R.v27828, N.v27828.
  unfold R.v6, N.v6.
  rewrite !state_r1234_nr_5F1234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1234_nr_5F1234 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27829 (s : N.State) (i : N.Inputs) :
  R.v27829 (state s) (inputs i) = Zmod.unsigned (N.v27829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27829 s i)) at 1.
  unfold R.v27829, N.v27829.
  unfold R.v6, N.v6.
  rewrite !state_r1233_nr_5F1233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1233_nr_5F1233 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27830 (s : N.State) (i : N.Inputs) :
  R.v27830 (state s) (inputs i) = Zmod.unsigned (N.v27830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27830 s i)) at 1.
  unfold R.v27830, N.v27830.
  rewrite ?node_27828.
  rewrite ?node_27829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27831 (s : N.State) (i : N.Inputs) :
  R.v27831 (state s) (inputs i) = Zmod.unsigned (N.v27831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27831 s i)) at 1.
  unfold R.v27831, N.v27831.
  unfold R.v16484, N.v16484.
  rewrite ?node_27830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27832 (s : N.State) (i : N.Inputs) :
  R.v27832 (state s) (inputs i) = Zmod.unsigned (N.v27832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27832 s i)) at 1.
  unfold R.v27832, N.v27832.
  rewrite ?node_27825.
  rewrite ?node_27826.
  rewrite ?node_27827.
  rewrite ?node_27831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27833 (s : N.State) (i : N.Inputs) :
  R.v27833 (state s) (inputs i) = Zmod.unsigned (N.v27833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27833 s i)) at 1.
  unfold R.v27833, N.v27833.
  unfold R.v6, N.v6.
  rewrite ?node_27832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27834 (s : N.State) (i : N.Inputs) :
  R.v27834 (state s) (inputs i) = Zmod.unsigned (N.v27834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27834 s i)) at 1.
  unfold R.v27834, N.v27834.
  rewrite ?node_10789.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27835 (s : N.State) (i : N.Inputs) :
  R.v27835 (state s) (inputs i) = Zmod.unsigned (N.v27835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27835 s i)) at 1.
  unfold R.v27835, N.v27835.
  unfold R.v6, N.v6.
  rewrite ?node_10949.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27836 (s : N.State) (i : N.Inputs) :
  R.v27836 (state s) (inputs i) = Zmod.unsigned (N.v27836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27836 s i)) at 1.
  unfold R.v27836, N.v27836.
  unfold R.v6, N.v6.
  rewrite ?node_11011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27837 (s : N.State) (i : N.Inputs) :
  R.v27837 (state s) (inputs i) = Zmod.unsigned (N.v27837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27837 s i)) at 1.
  unfold R.v27837, N.v27837.
  rewrite ?node_27834.
  rewrite ?node_27835.
  rewrite ?node_27836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27838 (s : N.State) (i : N.Inputs) :
  R.v27838 (state s) (inputs i) = Zmod.unsigned (N.v27838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27838 s i)) at 1.
  unfold R.v27838, N.v27838.
  rewrite ?node_27833.
  rewrite ?node_27837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27839 (s : N.State) (i : N.Inputs) :
  R.v27839 (state s) (inputs i) = Zmod.unsigned (N.v27839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27839 s i)) at 1.
  unfold R.v27839, N.v27839.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27840 (s : N.State) (i : N.Inputs) :
  R.v27840 (state s) (inputs i) = Zmod.unsigned (N.v27840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27840 s i)) at 1.
  unfold R.v27840, N.v27840.
  unfold R.v16463, N.v16463.
  rewrite !state_r1235_nr_5F1235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1235_nr_5F1235 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27841 (s : N.State) (i : N.Inputs) :
  R.v27841 (state s) (inputs i) = Zmod.unsigned (N.v27841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27841 s i)) at 1.
  unfold R.v27841, N.v27841.
  unfold R.v6, N.v6.
  rewrite !state_r1234_nr_5F1234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1234_nr_5F1234 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27842 (s : N.State) (i : N.Inputs) :
  R.v27842 (state s) (inputs i) = Zmod.unsigned (N.v27842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27842 s i)) at 1.
  unfold R.v27842, N.v27842.
  unfold R.v6, N.v6.
  rewrite !state_r1233_nr_5F1233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1233_nr_5F1233 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27843 (s : N.State) (i : N.Inputs) :
  R.v27843 (state s) (inputs i) = Zmod.unsigned (N.v27843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27843 s i)) at 1.
  unfold R.v27843, N.v27843.
  rewrite ?node_27841.
  rewrite ?node_27842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27844 (s : N.State) (i : N.Inputs) :
  R.v27844 (state s) (inputs i) = Zmod.unsigned (N.v27844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27844 s i)) at 1.
  unfold R.v27844, N.v27844.
  unfold R.v16484, N.v16484.
  rewrite ?node_27843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27845 (s : N.State) (i : N.Inputs) :
  R.v27845 (state s) (inputs i) = Zmod.unsigned (N.v27845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27845 s i)) at 1.
  unfold R.v27845, N.v27845.
  rewrite ?node_27840.
  rewrite ?node_27844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27846 (s : N.State) (i : N.Inputs) :
  R.v27846 (state s) (inputs i) = Zmod.unsigned (N.v27846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27846 s i)) at 1.
  unfold R.v27846, N.v27846.
  unfold R.v6, N.v6.
  rewrite ?node_27845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27847 (s : N.State) (i : N.Inputs) :
  R.v27847 (state s) (inputs i) = Zmod.unsigned (N.v27847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27847 s i)) at 1.
  unfold R.v27847, N.v27847.
  rewrite ?node_10784.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27848 (s : N.State) (i : N.Inputs) :
  R.v27848 (state s) (inputs i) = Zmod.unsigned (N.v27848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27848 s i)) at 1.
  unfold R.v27848, N.v27848.
  unfold R.v6, N.v6.
  rewrite ?node_10949.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27849 (s : N.State) (i : N.Inputs) :
  R.v27849 (state s) (inputs i) = Zmod.unsigned (N.v27849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27849 s i)) at 1.
  unfold R.v27849, N.v27849.
  rewrite ?node_27847.
  rewrite ?node_27848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27850 (s : N.State) (i : N.Inputs) :
  R.v27850 (state s) (inputs i) = Zmod.unsigned (N.v27850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27850 s i)) at 1.
  unfold R.v27850, N.v27850.
  rewrite ?node_27846.
  rewrite ?node_27849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27851 (s : N.State) (i : N.Inputs) :
  R.v27851 (state s) (inputs i) = Zmod.unsigned (N.v27851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27851 s i)) at 1.
  unfold R.v27851, N.v27851.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27852 (s : N.State) (i : N.Inputs) :
  R.v27852 (state s) (inputs i) = Zmod.unsigned (N.v27852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27852 s i)) at 1.
  unfold R.v27852, N.v27852.
  rewrite ?node_10788.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27853 (s : N.State) (i : N.Inputs) :
  R.v27853 (state s) (inputs i) = Zmod.unsigned (N.v27853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27853 s i)) at 1.
  unfold R.v27853, N.v27853.
  unfold R.v6, N.v6.
  rewrite !state_r1236_nr_5F1236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1236_nr_5F1236 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27854 (s : N.State) (i : N.Inputs) :
  R.v27854 (state s) (inputs i) = Zmod.unsigned (N.v27854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27854 s i)) at 1.
  unfold R.v27854, N.v27854.
  unfold R.v6, N.v6.
  rewrite ?node_10784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27855 (s : N.State) (i : N.Inputs) :
  R.v27855 (state s) (inputs i) = Zmod.unsigned (N.v27855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27855 s i)) at 1.
  unfold R.v27855, N.v27855.
  rewrite ?node_27853.
  rewrite ?node_27854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27856 (s : N.State) (i : N.Inputs) :
  R.v27856 (state s) (inputs i) = Zmod.unsigned (N.v27856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27856 s i)) at 1.
  unfold R.v27856, N.v27856.
  unfold R.v16484, N.v16484.
  rewrite ?node_27855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27857 (s : N.State) (i : N.Inputs) :
  R.v27857 (state s) (inputs i) = Zmod.unsigned (N.v27857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27857 s i)) at 1.
  unfold R.v27857, N.v27857.
  rewrite ?node_27852.
  rewrite ?node_27856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27858 (s : N.State) (i : N.Inputs) :
  R.v27858 (state s) (inputs i) = Zmod.unsigned (N.v27858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27858 s i)) at 1.
  unfold R.v27858, N.v27858.
  unfold R.v6, N.v6.
  rewrite ?node_27857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27859 (s : N.State) (i : N.Inputs) :
  R.v27859 (state s) (inputs i) = Zmod.unsigned (N.v27859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27859 s i)) at 1.
  unfold R.v27859, N.v27859.
  rewrite ?node_10789.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27860 (s : N.State) (i : N.Inputs) :
  R.v27860 (state s) (inputs i) = Zmod.unsigned (N.v27860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27860 s i)) at 1.
  unfold R.v27860, N.v27860.
  unfold R.v6, N.v6.
  rewrite ?node_11011.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27861 (s : N.State) (i : N.Inputs) :
  R.v27861 (state s) (inputs i) = Zmod.unsigned (N.v27861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27861 s i)) at 1.
  unfold R.v27861, N.v27861.
  rewrite ?node_27859.
  rewrite ?node_27860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27862 (s : N.State) (i : N.Inputs) :
  R.v27862 (state s) (inputs i) = Zmod.unsigned (N.v27862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27862 s i)) at 1.
  unfold R.v27862, N.v27862.
  rewrite ?node_27858.
  rewrite ?node_27861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27863 (s : N.State) (i : N.Inputs) :
  R.v27863 (state s) (inputs i) = Zmod.unsigned (N.v27863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27863 s i)) at 1.
  unfold R.v27863, N.v27863.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27864 (s : N.State) (i : N.Inputs) :
  R.v27864 (state s) (inputs i) = Zmod.unsigned (N.v27864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27864 s i)) at 1.
  unfold R.v27864, N.v27864.
  rewrite ?node_10800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27865 (s : N.State) (i : N.Inputs) :
  R.v27865 (state s) (inputs i) = Zmod.unsigned (N.v27865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27865 s i)) at 1.
  unfold R.v27865, N.v27865.
  unfold R.v16463, N.v16463.
  rewrite !state_r1240_nr_5F1240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1240_nr_5F1240 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27866 (s : N.State) (i : N.Inputs) :
  R.v27866 (state s) (inputs i) = Zmod.unsigned (N.v27866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27866 s i)) at 1.
  unfold R.v27866, N.v27866.
  unfold R.v16463, N.v16463.
  rewrite !state_r1239_nr_5F1239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1239_nr_5F1239 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27867 (s : N.State) (i : N.Inputs) :
  R.v27867 (state s) (inputs i) = Zmod.unsigned (N.v27867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27867 s i)) at 1.
  unfold R.v27867, N.v27867.
  unfold R.v6, N.v6.
  rewrite !state_r1238_nr_5F1238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1238_nr_5F1238 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27868 (s : N.State) (i : N.Inputs) :
  R.v27868 (state s) (inputs i) = Zmod.unsigned (N.v27868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27868 s i)) at 1.
  unfold R.v27868, N.v27868.
  unfold R.v6, N.v6.
  rewrite !state_r1237_nr_5F1237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1237_nr_5F1237 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27869 (s : N.State) (i : N.Inputs) :
  R.v27869 (state s) (inputs i) = Zmod.unsigned (N.v27869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27869 s i)) at 1.
  unfold R.v27869, N.v27869.
  rewrite ?node_27867.
  rewrite ?node_27868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27870 (s : N.State) (i : N.Inputs) :
  R.v27870 (state s) (inputs i) = Zmod.unsigned (N.v27870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27870 s i)) at 1.
  unfold R.v27870, N.v27870.
  unfold R.v16484, N.v16484.
  rewrite ?node_27869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27871 (s : N.State) (i : N.Inputs) :
  R.v27871 (state s) (inputs i) = Zmod.unsigned (N.v27871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27871 s i)) at 1.
  unfold R.v27871, N.v27871.
  rewrite ?node_27864.
  rewrite ?node_27865.
  rewrite ?node_27866.
  rewrite ?node_27870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27872 (s : N.State) (i : N.Inputs) :
  R.v27872 (state s) (inputs i) = Zmod.unsigned (N.v27872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27872 s i)) at 1.
  unfold R.v27872, N.v27872.
  unfold R.v6, N.v6.
  rewrite ?node_27871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27873 (s : N.State) (i : N.Inputs) :
  R.v27873 (state s) (inputs i) = Zmod.unsigned (N.v27873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27873 s i)) at 1.
  unfold R.v27873, N.v27873.
  rewrite ?node_10801.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27874 (s : N.State) (i : N.Inputs) :
  R.v27874 (state s) (inputs i) = Zmod.unsigned (N.v27874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27874 s i)) at 1.
  unfold R.v27874, N.v27874.
  unfold R.v6, N.v6.
  rewrite ?node_10961.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27875 (s : N.State) (i : N.Inputs) :
  R.v27875 (state s) (inputs i) = Zmod.unsigned (N.v27875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27875 s i)) at 1.
  unfold R.v27875, N.v27875.
  unfold R.v6, N.v6.
  rewrite ?node_11014.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27876 (s : N.State) (i : N.Inputs) :
  R.v27876 (state s) (inputs i) = Zmod.unsigned (N.v27876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27876 s i)) at 1.
  unfold R.v27876, N.v27876.
  rewrite ?node_27873.
  rewrite ?node_27874.
  rewrite ?node_27875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27877 (s : N.State) (i : N.Inputs) :
  R.v27877 (state s) (inputs i) = Zmod.unsigned (N.v27877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27877 s i)) at 1.
  unfold R.v27877, N.v27877.
  rewrite ?node_27872.
  rewrite ?node_27876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27878 (s : N.State) (i : N.Inputs) :
  R.v27878 (state s) (inputs i) = Zmod.unsigned (N.v27878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27878 s i)) at 1.
  unfold R.v27878, N.v27878.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27879 (s : N.State) (i : N.Inputs) :
  R.v27879 (state s) (inputs i) = Zmod.unsigned (N.v27879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27879 s i)) at 1.
  unfold R.v27879, N.v27879.
  unfold R.v16463, N.v16463.
  rewrite !state_r1239_nr_5F1239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1239_nr_5F1239 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27880 (s : N.State) (i : N.Inputs) :
  R.v27880 (state s) (inputs i) = Zmod.unsigned (N.v27880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27880 s i)) at 1.
  unfold R.v27880, N.v27880.
  unfold R.v6, N.v6.
  rewrite !state_r1238_nr_5F1238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1238_nr_5F1238 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27881 (s : N.State) (i : N.Inputs) :
  R.v27881 (state s) (inputs i) = Zmod.unsigned (N.v27881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27881 s i)) at 1.
  unfold R.v27881, N.v27881.
  unfold R.v6, N.v6.
  rewrite !state_r1237_nr_5F1237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1237_nr_5F1237 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27882 (s : N.State) (i : N.Inputs) :
  R.v27882 (state s) (inputs i) = Zmod.unsigned (N.v27882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27882 s i)) at 1.
  unfold R.v27882, N.v27882.
  rewrite ?node_27880.
  rewrite ?node_27881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27883 (s : N.State) (i : N.Inputs) :
  R.v27883 (state s) (inputs i) = Zmod.unsigned (N.v27883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27883 s i)) at 1.
  unfold R.v27883, N.v27883.
  unfold R.v16484, N.v16484.
  rewrite ?node_27882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27884 (s : N.State) (i : N.Inputs) :
  R.v27884 (state s) (inputs i) = Zmod.unsigned (N.v27884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27884 s i)) at 1.
  unfold R.v27884, N.v27884.
  rewrite ?node_27879.
  rewrite ?node_27883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27885 (s : N.State) (i : N.Inputs) :
  R.v27885 (state s) (inputs i) = Zmod.unsigned (N.v27885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27885 s i)) at 1.
  unfold R.v27885, N.v27885.
  unfold R.v6, N.v6.
  rewrite ?node_27884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27886 (s : N.State) (i : N.Inputs) :
  R.v27886 (state s) (inputs i) = Zmod.unsigned (N.v27886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27886 s i)) at 1.
  unfold R.v27886, N.v27886.
  rewrite ?node_10796.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27887 (s : N.State) (i : N.Inputs) :
  R.v27887 (state s) (inputs i) = Zmod.unsigned (N.v27887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27887 s i)) at 1.
  unfold R.v27887, N.v27887.
  unfold R.v6, N.v6.
  rewrite ?node_10961.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27888 (s : N.State) (i : N.Inputs) :
  R.v27888 (state s) (inputs i) = Zmod.unsigned (N.v27888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27888 s i)) at 1.
  unfold R.v27888, N.v27888.
  rewrite ?node_27886.
  rewrite ?node_27887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27889 (s : N.State) (i : N.Inputs) :
  R.v27889 (state s) (inputs i) = Zmod.unsigned (N.v27889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27889 s i)) at 1.
  unfold R.v27889, N.v27889.
  rewrite ?node_27885.
  rewrite ?node_27888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27890 (s : N.State) (i : N.Inputs) :
  R.v27890 (state s) (inputs i) = Zmod.unsigned (N.v27890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27890 s i)) at 1.
  unfold R.v27890, N.v27890.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27891 (s : N.State) (i : N.Inputs) :
  R.v27891 (state s) (inputs i) = Zmod.unsigned (N.v27891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27891 s i)) at 1.
  unfold R.v27891, N.v27891.
  rewrite ?node_10800.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27892 (s : N.State) (i : N.Inputs) :
  R.v27892 (state s) (inputs i) = Zmod.unsigned (N.v27892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27892 s i)) at 1.
  unfold R.v27892, N.v27892.
  unfold R.v6, N.v6.
  rewrite !state_r1240_nr_5F1240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1240_nr_5F1240 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27893 (s : N.State) (i : N.Inputs) :
  R.v27893 (state s) (inputs i) = Zmod.unsigned (N.v27893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27893 s i)) at 1.
  unfold R.v27893, N.v27893.
  unfold R.v6, N.v6.
  rewrite ?node_10796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27894 (s : N.State) (i : N.Inputs) :
  R.v27894 (state s) (inputs i) = Zmod.unsigned (N.v27894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27894 s i)) at 1.
  unfold R.v27894, N.v27894.
  rewrite ?node_27892.
  rewrite ?node_27893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27895 (s : N.State) (i : N.Inputs) :
  R.v27895 (state s) (inputs i) = Zmod.unsigned (N.v27895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27895 s i)) at 1.
  unfold R.v27895, N.v27895.
  unfold R.v16484, N.v16484.
  rewrite ?node_27894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27896 (s : N.State) (i : N.Inputs) :
  R.v27896 (state s) (inputs i) = Zmod.unsigned (N.v27896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27896 s i)) at 1.
  unfold R.v27896, N.v27896.
  rewrite ?node_27891.
  rewrite ?node_27895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27897 (s : N.State) (i : N.Inputs) :
  R.v27897 (state s) (inputs i) = Zmod.unsigned (N.v27897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27897 s i)) at 1.
  unfold R.v27897, N.v27897.
  unfold R.v6, N.v6.
  rewrite ?node_27896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27898 (s : N.State) (i : N.Inputs) :
  R.v27898 (state s) (inputs i) = Zmod.unsigned (N.v27898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27898 s i)) at 1.
  unfold R.v27898, N.v27898.
  rewrite ?node_10801.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27899 (s : N.State) (i : N.Inputs) :
  R.v27899 (state s) (inputs i) = Zmod.unsigned (N.v27899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27899 s i)) at 1.
  unfold R.v27899, N.v27899.
  unfold R.v6, N.v6.
  rewrite ?node_11014.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27900 (s : N.State) (i : N.Inputs) :
  R.v27900 (state s) (inputs i) = Zmod.unsigned (N.v27900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27900 s i)) at 1.
  unfold R.v27900, N.v27900.
  rewrite ?node_27898.
  rewrite ?node_27899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27901 (s : N.State) (i : N.Inputs) :
  R.v27901 (state s) (inputs i) = Zmod.unsigned (N.v27901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27901 s i)) at 1.
  unfold R.v27901, N.v27901.
  rewrite ?node_27897.
  rewrite ?node_27900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27902 (s : N.State) (i : N.Inputs) :
  R.v27902 (state s) (inputs i) = Zmod.unsigned (N.v27902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27902 s i)) at 1.
  unfold R.v27902, N.v27902.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27903 (s : N.State) (i : N.Inputs) :
  R.v27903 (state s) (inputs i) = Zmod.unsigned (N.v27903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27903 s i)) at 1.
  unfold R.v27903, N.v27903.
  rewrite ?node_10807.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27904 (s : N.State) (i : N.Inputs) :
  R.v27904 (state s) (inputs i) = Zmod.unsigned (N.v27904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27904 s i)) at 1.
  unfold R.v27904, N.v27904.
  unfold R.v16463, N.v16463.
  rewrite !state_r1244_nr_5F1244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1244_nr_5F1244 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27905 (s : N.State) (i : N.Inputs) :
  R.v27905 (state s) (inputs i) = Zmod.unsigned (N.v27905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27905 s i)) at 1.
  unfold R.v27905, N.v27905.
  unfold R.v16463, N.v16463.
  rewrite !state_r1243_nr_5F1243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1243_nr_5F1243 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27906 (s : N.State) (i : N.Inputs) :
  R.v27906 (state s) (inputs i) = Zmod.unsigned (N.v27906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27906 s i)) at 1.
  unfold R.v27906, N.v27906.
  unfold R.v6, N.v6.
  rewrite !state_r1242_nr_5F1242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1242_nr_5F1242 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27907 (s : N.State) (i : N.Inputs) :
  R.v27907 (state s) (inputs i) = Zmod.unsigned (N.v27907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27907 s i)) at 1.
  unfold R.v27907, N.v27907.
  unfold R.v6, N.v6.
  rewrite !state_r1241_nr_5F1241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1241_nr_5F1241 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27908 (s : N.State) (i : N.Inputs) :
  R.v27908 (state s) (inputs i) = Zmod.unsigned (N.v27908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27908 s i)) at 1.
  unfold R.v27908, N.v27908.
  rewrite ?node_27906.
  rewrite ?node_27907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27909 (s : N.State) (i : N.Inputs) :
  R.v27909 (state s) (inputs i) = Zmod.unsigned (N.v27909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27909 s i)) at 1.
  unfold R.v27909, N.v27909.
  unfold R.v16484, N.v16484.
  rewrite ?node_27908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27910 (s : N.State) (i : N.Inputs) :
  R.v27910 (state s) (inputs i) = Zmod.unsigned (N.v27910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27910 s i)) at 1.
  unfold R.v27910, N.v27910.
  rewrite ?node_27903.
  rewrite ?node_27904.
  rewrite ?node_27905.
  rewrite ?node_27909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27911 (s : N.State) (i : N.Inputs) :
  R.v27911 (state s) (inputs i) = Zmod.unsigned (N.v27911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27911 s i)) at 1.
  unfold R.v27911, N.v27911.
  unfold R.v6, N.v6.
  rewrite ?node_27910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27912 (s : N.State) (i : N.Inputs) :
  R.v27912 (state s) (inputs i) = Zmod.unsigned (N.v27912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27912 s i)) at 1.
  unfold R.v27912, N.v27912.
  rewrite ?node_10808.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27913 (s : N.State) (i : N.Inputs) :
  R.v27913 (state s) (inputs i) = Zmod.unsigned (N.v27913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27913 s i)) at 1.
  unfold R.v27913, N.v27913.
  unfold R.v6, N.v6.
  rewrite ?node_10968.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27914 (s : N.State) (i : N.Inputs) :
  R.v27914 (state s) (inputs i) = Zmod.unsigned (N.v27914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27914 s i)) at 1.
  unfold R.v27914, N.v27914.
  unfold R.v6, N.v6.
  rewrite ?node_11018.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27915 (s : N.State) (i : N.Inputs) :
  R.v27915 (state s) (inputs i) = Zmod.unsigned (N.v27915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27915 s i)) at 1.
  unfold R.v27915, N.v27915.
  rewrite ?node_27912.
  rewrite ?node_27913.
  rewrite ?node_27914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27916 (s : N.State) (i : N.Inputs) :
  R.v27916 (state s) (inputs i) = Zmod.unsigned (N.v27916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27916 s i)) at 1.
  unfold R.v27916, N.v27916.
  rewrite ?node_27911.
  rewrite ?node_27915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27917 (s : N.State) (i : N.Inputs) :
  R.v27917 (state s) (inputs i) = Zmod.unsigned (N.v27917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27917 s i)) at 1.
  unfold R.v27917, N.v27917.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27918 (s : N.State) (i : N.Inputs) :
  R.v27918 (state s) (inputs i) = Zmod.unsigned (N.v27918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27918 s i)) at 1.
  unfold R.v27918, N.v27918.
  unfold R.v16463, N.v16463.
  rewrite !state_r1243_nr_5F1243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1243_nr_5F1243 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27919 (s : N.State) (i : N.Inputs) :
  R.v27919 (state s) (inputs i) = Zmod.unsigned (N.v27919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27919 s i)) at 1.
  unfold R.v27919, N.v27919.
  unfold R.v6, N.v6.
  rewrite !state_r1242_nr_5F1242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1242_nr_5F1242 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27920 (s : N.State) (i : N.Inputs) :
  R.v27920 (state s) (inputs i) = Zmod.unsigned (N.v27920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27920 s i)) at 1.
  unfold R.v27920, N.v27920.
  unfold R.v6, N.v6.
  rewrite !state_r1241_nr_5F1241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1241_nr_5F1241 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27921 (s : N.State) (i : N.Inputs) :
  R.v27921 (state s) (inputs i) = Zmod.unsigned (N.v27921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27921 s i)) at 1.
  unfold R.v27921, N.v27921.
  rewrite ?node_27919.
  rewrite ?node_27920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27922 (s : N.State) (i : N.Inputs) :
  R.v27922 (state s) (inputs i) = Zmod.unsigned (N.v27922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27922 s i)) at 1.
  unfold R.v27922, N.v27922.
  unfold R.v16484, N.v16484.
  rewrite ?node_27921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27923 (s : N.State) (i : N.Inputs) :
  R.v27923 (state s) (inputs i) = Zmod.unsigned (N.v27923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27923 s i)) at 1.
  unfold R.v27923, N.v27923.
  rewrite ?node_27918.
  rewrite ?node_27922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27924 (s : N.State) (i : N.Inputs) :
  R.v27924 (state s) (inputs i) = Zmod.unsigned (N.v27924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27924 s i)) at 1.
  unfold R.v27924, N.v27924.
  unfold R.v6, N.v6.
  rewrite ?node_27923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27925 (s : N.State) (i : N.Inputs) :
  R.v27925 (state s) (inputs i) = Zmod.unsigned (N.v27925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27925 s i)) at 1.
  unfold R.v27925, N.v27925.
  rewrite ?node_10803.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27926 (s : N.State) (i : N.Inputs) :
  R.v27926 (state s) (inputs i) = Zmod.unsigned (N.v27926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27926 s i)) at 1.
  unfold R.v27926, N.v27926.
  unfold R.v6, N.v6.
  rewrite ?node_10968.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27927 (s : N.State) (i : N.Inputs) :
  R.v27927 (state s) (inputs i) = Zmod.unsigned (N.v27927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27927 s i)) at 1.
  unfold R.v27927, N.v27927.
  rewrite ?node_27925.
  rewrite ?node_27926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27928 (s : N.State) (i : N.Inputs) :
  R.v27928 (state s) (inputs i) = Zmod.unsigned (N.v27928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27928 s i)) at 1.
  unfold R.v27928, N.v27928.
  rewrite ?node_27924.
  rewrite ?node_27927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27929 (s : N.State) (i : N.Inputs) :
  R.v27929 (state s) (inputs i) = Zmod.unsigned (N.v27929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27929 s i)) at 1.
  unfold R.v27929, N.v27929.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27930 (s : N.State) (i : N.Inputs) :
  R.v27930 (state s) (inputs i) = Zmod.unsigned (N.v27930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27930 s i)) at 1.
  unfold R.v27930, N.v27930.
  rewrite ?node_10807.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27931 (s : N.State) (i : N.Inputs) :
  R.v27931 (state s) (inputs i) = Zmod.unsigned (N.v27931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27931 s i)) at 1.
  unfold R.v27931, N.v27931.
  unfold R.v6, N.v6.
  rewrite !state_r1244_nr_5F1244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1244_nr_5F1244 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27932 (s : N.State) (i : N.Inputs) :
  R.v27932 (state s) (inputs i) = Zmod.unsigned (N.v27932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27932 s i)) at 1.
  unfold R.v27932, N.v27932.
  unfold R.v6, N.v6.
  rewrite ?node_10803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27933 (s : N.State) (i : N.Inputs) :
  R.v27933 (state s) (inputs i) = Zmod.unsigned (N.v27933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27933 s i)) at 1.
  unfold R.v27933, N.v27933.
  rewrite ?node_27931.
  rewrite ?node_27932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27934 (s : N.State) (i : N.Inputs) :
  R.v27934 (state s) (inputs i) = Zmod.unsigned (N.v27934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27934 s i)) at 1.
  unfold R.v27934, N.v27934.
  unfold R.v16484, N.v16484.
  rewrite ?node_27933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27935 (s : N.State) (i : N.Inputs) :
  R.v27935 (state s) (inputs i) = Zmod.unsigned (N.v27935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27935 s i)) at 1.
  unfold R.v27935, N.v27935.
  rewrite ?node_27930.
  rewrite ?node_27934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27936 (s : N.State) (i : N.Inputs) :
  R.v27936 (state s) (inputs i) = Zmod.unsigned (N.v27936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27936 s i)) at 1.
  unfold R.v27936, N.v27936.
  unfold R.v6, N.v6.
  rewrite ?node_27935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27937 (s : N.State) (i : N.Inputs) :
  R.v27937 (state s) (inputs i) = Zmod.unsigned (N.v27937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27937 s i)) at 1.
  unfold R.v27937, N.v27937.
  rewrite ?node_10808.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27938 (s : N.State) (i : N.Inputs) :
  R.v27938 (state s) (inputs i) = Zmod.unsigned (N.v27938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27938 s i)) at 1.
  unfold R.v27938, N.v27938.
  unfold R.v6, N.v6.
  rewrite ?node_11018.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27939 (s : N.State) (i : N.Inputs) :
  R.v27939 (state s) (inputs i) = Zmod.unsigned (N.v27939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27939 s i)) at 1.
  unfold R.v27939, N.v27939.
  rewrite ?node_27937.
  rewrite ?node_27938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27940 (s : N.State) (i : N.Inputs) :
  R.v27940 (state s) (inputs i) = Zmod.unsigned (N.v27940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27940 s i)) at 1.
  unfold R.v27940, N.v27940.
  rewrite ?node_27936.
  rewrite ?node_27939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27941 (s : N.State) (i : N.Inputs) :
  R.v27941 (state s) (inputs i) = Zmod.unsigned (N.v27941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27941 s i)) at 1.
  unfold R.v27941, N.v27941.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27942 (s : N.State) (i : N.Inputs) :
  R.v27942 (state s) (inputs i) = Zmod.unsigned (N.v27942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27942 s i)) at 1.
  unfold R.v27942, N.v27942.
  rewrite ?node_10815.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27943 (s : N.State) (i : N.Inputs) :
  R.v27943 (state s) (inputs i) = Zmod.unsigned (N.v27943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27943 s i)) at 1.
  unfold R.v27943, N.v27943.
  unfold R.v16463, N.v16463.
  rewrite !state_r1248_nr_5F1248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1248_nr_5F1248 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27944 (s : N.State) (i : N.Inputs) :
  R.v27944 (state s) (inputs i) = Zmod.unsigned (N.v27944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27944 s i)) at 1.
  unfold R.v27944, N.v27944.
  unfold R.v16463, N.v16463.
  rewrite !state_r1247_nr_5F1247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1247_nr_5F1247 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27945 (s : N.State) (i : N.Inputs) :
  R.v27945 (state s) (inputs i) = Zmod.unsigned (N.v27945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27945 s i)) at 1.
  unfold R.v27945, N.v27945.
  unfold R.v6, N.v6.
  rewrite !state_r1246_nr_5F1246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1246_nr_5F1246 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27946 (s : N.State) (i : N.Inputs) :
  R.v27946 (state s) (inputs i) = Zmod.unsigned (N.v27946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27946 s i)) at 1.
  unfold R.v27946, N.v27946.
  unfold R.v6, N.v6.
  rewrite !state_r1245_nr_5F1245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1245_nr_5F1245 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27947 (s : N.State) (i : N.Inputs) :
  R.v27947 (state s) (inputs i) = Zmod.unsigned (N.v27947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27947 s i)) at 1.
  unfold R.v27947, N.v27947.
  rewrite ?node_27945.
  rewrite ?node_27946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27948 (s : N.State) (i : N.Inputs) :
  R.v27948 (state s) (inputs i) = Zmod.unsigned (N.v27948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27948 s i)) at 1.
  unfold R.v27948, N.v27948.
  unfold R.v16484, N.v16484.
  rewrite ?node_27947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27949 (s : N.State) (i : N.Inputs) :
  R.v27949 (state s) (inputs i) = Zmod.unsigned (N.v27949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27949 s i)) at 1.
  unfold R.v27949, N.v27949.
  rewrite ?node_27942.
  rewrite ?node_27943.
  rewrite ?node_27944.
  rewrite ?node_27948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27950 (s : N.State) (i : N.Inputs) :
  R.v27950 (state s) (inputs i) = Zmod.unsigned (N.v27950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27950 s i)) at 1.
  unfold R.v27950, N.v27950.
  unfold R.v6, N.v6.
  rewrite ?node_27949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27951 (s : N.State) (i : N.Inputs) :
  R.v27951 (state s) (inputs i) = Zmod.unsigned (N.v27951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27951 s i)) at 1.
  unfold R.v27951, N.v27951.
  rewrite ?node_10816.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27952 (s : N.State) (i : N.Inputs) :
  R.v27952 (state s) (inputs i) = Zmod.unsigned (N.v27952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27952 s i)) at 1.
  unfold R.v27952, N.v27952.
  unfold R.v6, N.v6.
  rewrite ?node_10976.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27953 (s : N.State) (i : N.Inputs) :
  R.v27953 (state s) (inputs i) = Zmod.unsigned (N.v27953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27953 s i)) at 1.
  unfold R.v27953, N.v27953.
  unfold R.v6, N.v6.
  rewrite ?node_11022.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27954 (s : N.State) (i : N.Inputs) :
  R.v27954 (state s) (inputs i) = Zmod.unsigned (N.v27954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27954 s i)) at 1.
  unfold R.v27954, N.v27954.
  rewrite ?node_27951.
  rewrite ?node_27952.
  rewrite ?node_27953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27955 (s : N.State) (i : N.Inputs) :
  R.v27955 (state s) (inputs i) = Zmod.unsigned (N.v27955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27955 s i)) at 1.
  unfold R.v27955, N.v27955.
  rewrite ?node_27950.
  rewrite ?node_27954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27956 (s : N.State) (i : N.Inputs) :
  R.v27956 (state s) (inputs i) = Zmod.unsigned (N.v27956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27956 s i)) at 1.
  unfold R.v27956, N.v27956.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27957 (s : N.State) (i : N.Inputs) :
  R.v27957 (state s) (inputs i) = Zmod.unsigned (N.v27957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27957 s i)) at 1.
  unfold R.v27957, N.v27957.
  unfold R.v16463, N.v16463.
  rewrite !state_r1247_nr_5F1247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1247_nr_5F1247 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27958 (s : N.State) (i : N.Inputs) :
  R.v27958 (state s) (inputs i) = Zmod.unsigned (N.v27958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27958 s i)) at 1.
  unfold R.v27958, N.v27958.
  unfold R.v6, N.v6.
  rewrite !state_r1246_nr_5F1246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1246_nr_5F1246 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27959 (s : N.State) (i : N.Inputs) :
  R.v27959 (state s) (inputs i) = Zmod.unsigned (N.v27959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27959 s i)) at 1.
  unfold R.v27959, N.v27959.
  unfold R.v6, N.v6.
  rewrite !state_r1245_nr_5F1245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1245_nr_5F1245 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27960 (s : N.State) (i : N.Inputs) :
  R.v27960 (state s) (inputs i) = Zmod.unsigned (N.v27960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27960 s i)) at 1.
  unfold R.v27960, N.v27960.
  rewrite ?node_27958.
  rewrite ?node_27959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27961 (s : N.State) (i : N.Inputs) :
  R.v27961 (state s) (inputs i) = Zmod.unsigned (N.v27961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27961 s i)) at 1.
  unfold R.v27961, N.v27961.
  unfold R.v16484, N.v16484.
  rewrite ?node_27960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27962 (s : N.State) (i : N.Inputs) :
  R.v27962 (state s) (inputs i) = Zmod.unsigned (N.v27962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27962 s i)) at 1.
  unfold R.v27962, N.v27962.
  rewrite ?node_27957.
  rewrite ?node_27961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27963 (s : N.State) (i : N.Inputs) :
  R.v27963 (state s) (inputs i) = Zmod.unsigned (N.v27963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27963 s i)) at 1.
  unfold R.v27963, N.v27963.
  unfold R.v6, N.v6.
  rewrite ?node_27962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27964 (s : N.State) (i : N.Inputs) :
  R.v27964 (state s) (inputs i) = Zmod.unsigned (N.v27964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27964 s i)) at 1.
  unfold R.v27964, N.v27964.
  rewrite ?node_10811.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27965 (s : N.State) (i : N.Inputs) :
  R.v27965 (state s) (inputs i) = Zmod.unsigned (N.v27965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27965 s i)) at 1.
  unfold R.v27965, N.v27965.
  unfold R.v6, N.v6.
  rewrite ?node_10976.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27966 (s : N.State) (i : N.Inputs) :
  R.v27966 (state s) (inputs i) = Zmod.unsigned (N.v27966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27966 s i)) at 1.
  unfold R.v27966, N.v27966.
  rewrite ?node_27964.
  rewrite ?node_27965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27967 (s : N.State) (i : N.Inputs) :
  R.v27967 (state s) (inputs i) = Zmod.unsigned (N.v27967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27967 s i)) at 1.
  unfold R.v27967, N.v27967.
  rewrite ?node_27963.
  rewrite ?node_27966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27968 (s : N.State) (i : N.Inputs) :
  R.v27968 (state s) (inputs i) = Zmod.unsigned (N.v27968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27968 s i)) at 1.
  unfold R.v27968, N.v27968.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27969 (s : N.State) (i : N.Inputs) :
  R.v27969 (state s) (inputs i) = Zmod.unsigned (N.v27969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27969 s i)) at 1.
  unfold R.v27969, N.v27969.
  rewrite ?node_10815.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27970 (s : N.State) (i : N.Inputs) :
  R.v27970 (state s) (inputs i) = Zmod.unsigned (N.v27970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27970 s i)) at 1.
  unfold R.v27970, N.v27970.
  unfold R.v6, N.v6.
  rewrite !state_r1248_nr_5F1248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1248_nr_5F1248 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27971 (s : N.State) (i : N.Inputs) :
  R.v27971 (state s) (inputs i) = Zmod.unsigned (N.v27971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27971 s i)) at 1.
  unfold R.v27971, N.v27971.
  unfold R.v6, N.v6.
  rewrite ?node_10811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27972 (s : N.State) (i : N.Inputs) :
  R.v27972 (state s) (inputs i) = Zmod.unsigned (N.v27972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27972 s i)) at 1.
  unfold R.v27972, N.v27972.
  rewrite ?node_27970.
  rewrite ?node_27971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27973 (s : N.State) (i : N.Inputs) :
  R.v27973 (state s) (inputs i) = Zmod.unsigned (N.v27973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27973 s i)) at 1.
  unfold R.v27973, N.v27973.
  unfold R.v16484, N.v16484.
  rewrite ?node_27972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27974 (s : N.State) (i : N.Inputs) :
  R.v27974 (state s) (inputs i) = Zmod.unsigned (N.v27974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27974 s i)) at 1.
  unfold R.v27974, N.v27974.
  rewrite ?node_27969.
  rewrite ?node_27973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27975 (s : N.State) (i : N.Inputs) :
  R.v27975 (state s) (inputs i) = Zmod.unsigned (N.v27975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27975 s i)) at 1.
  unfold R.v27975, N.v27975.
  unfold R.v6, N.v6.
  rewrite ?node_27974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27976 (s : N.State) (i : N.Inputs) :
  R.v27976 (state s) (inputs i) = Zmod.unsigned (N.v27976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27976 s i)) at 1.
  unfold R.v27976, N.v27976.
  rewrite ?node_10816.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27977 (s : N.State) (i : N.Inputs) :
  R.v27977 (state s) (inputs i) = Zmod.unsigned (N.v27977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27977 s i)) at 1.
  unfold R.v27977, N.v27977.
  unfold R.v6, N.v6.
  rewrite ?node_11022.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27978 (s : N.State) (i : N.Inputs) :
  R.v27978 (state s) (inputs i) = Zmod.unsigned (N.v27978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27978 s i)) at 1.
  unfold R.v27978, N.v27978.
  rewrite ?node_27976.
  rewrite ?node_27977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27979 (s : N.State) (i : N.Inputs) :
  R.v27979 (state s) (inputs i) = Zmod.unsigned (N.v27979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27979 s i)) at 1.
  unfold R.v27979, N.v27979.
  rewrite ?node_27975.
  rewrite ?node_27978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27980 (s : N.State) (i : N.Inputs) :
  R.v27980 (state s) (inputs i) = Zmod.unsigned (N.v27980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27980 s i)) at 1.
  unfold R.v27980, N.v27980.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27981 (s : N.State) (i : N.Inputs) :
  R.v27981 (state s) (inputs i) = Zmod.unsigned (N.v27981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27981 s i)) at 1.
  unfold R.v27981, N.v27981.
  rewrite ?node_10823.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27982 (s : N.State) (i : N.Inputs) :
  R.v27982 (state s) (inputs i) = Zmod.unsigned (N.v27982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27982 s i)) at 1.
  unfold R.v27982, N.v27982.
  unfold R.v16463, N.v16463.
  rewrite !state_r1252_nr_5F1252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1252_nr_5F1252 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27983 (s : N.State) (i : N.Inputs) :
  R.v27983 (state s) (inputs i) = Zmod.unsigned (N.v27983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27983 s i)) at 1.
  unfold R.v27983, N.v27983.
  unfold R.v16463, N.v16463.
  rewrite !state_r1251_nr_5F1251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1251_nr_5F1251 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27984 (s : N.State) (i : N.Inputs) :
  R.v27984 (state s) (inputs i) = Zmod.unsigned (N.v27984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27984 s i)) at 1.
  unfold R.v27984, N.v27984.
  unfold R.v6, N.v6.
  rewrite !state_r1250_nr_5F1250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1250_nr_5F1250 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27985 (s : N.State) (i : N.Inputs) :
  R.v27985 (state s) (inputs i) = Zmod.unsigned (N.v27985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27985 s i)) at 1.
  unfold R.v27985, N.v27985.
  unfold R.v6, N.v6.
  rewrite !state_r1249_nr_5F1249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1249_nr_5F1249 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27986 (s : N.State) (i : N.Inputs) :
  R.v27986 (state s) (inputs i) = Zmod.unsigned (N.v27986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27986 s i)) at 1.
  unfold R.v27986, N.v27986.
  rewrite ?node_27984.
  rewrite ?node_27985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27987 (s : N.State) (i : N.Inputs) :
  R.v27987 (state s) (inputs i) = Zmod.unsigned (N.v27987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27987 s i)) at 1.
  unfold R.v27987, N.v27987.
  unfold R.v16484, N.v16484.
  rewrite ?node_27986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27988 (s : N.State) (i : N.Inputs) :
  R.v27988 (state s) (inputs i) = Zmod.unsigned (N.v27988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27988 s i)) at 1.
  unfold R.v27988, N.v27988.
  rewrite ?node_27981.
  rewrite ?node_27982.
  rewrite ?node_27983.
  rewrite ?node_27987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27989 (s : N.State) (i : N.Inputs) :
  R.v27989 (state s) (inputs i) = Zmod.unsigned (N.v27989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27989 s i)) at 1.
  unfold R.v27989, N.v27989.
  unfold R.v6, N.v6.
  rewrite ?node_27988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27990 (s : N.State) (i : N.Inputs) :
  R.v27990 (state s) (inputs i) = Zmod.unsigned (N.v27990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27990 s i)) at 1.
  unfold R.v27990, N.v27990.
  rewrite ?node_10824.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27991 (s : N.State) (i : N.Inputs) :
  R.v27991 (state s) (inputs i) = Zmod.unsigned (N.v27991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27991 s i)) at 1.
  unfold R.v27991, N.v27991.
  unfold R.v6, N.v6.
  rewrite ?node_10984.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27992 (s : N.State) (i : N.Inputs) :
  R.v27992 (state s) (inputs i) = Zmod.unsigned (N.v27992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27992 s i)) at 1.
  unfold R.v27992, N.v27992.
  unfold R.v6, N.v6.
  rewrite ?node_11035.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27993 (s : N.State) (i : N.Inputs) :
  R.v27993 (state s) (inputs i) = Zmod.unsigned (N.v27993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27993 s i)) at 1.
  unfold R.v27993, N.v27993.
  rewrite ?node_27990.
  rewrite ?node_27991.
  rewrite ?node_27992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27994 (s : N.State) (i : N.Inputs) :
  R.v27994 (state s) (inputs i) = Zmod.unsigned (N.v27994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27994 s i)) at 1.
  unfold R.v27994, N.v27994.
  rewrite ?node_27989.
  rewrite ?node_27993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27995 (s : N.State) (i : N.Inputs) :
  R.v27995 (state s) (inputs i) = Zmod.unsigned (N.v27995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27995 s i)) at 1.
  unfold R.v27995, N.v27995.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27996 (s : N.State) (i : N.Inputs) :
  R.v27996 (state s) (inputs i) = Zmod.unsigned (N.v27996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27996 s i)) at 1.
  unfold R.v27996, N.v27996.
  unfold R.v16463, N.v16463.
  rewrite !state_r1251_nr_5F1251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1251_nr_5F1251 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27997 (s : N.State) (i : N.Inputs) :
  R.v27997 (state s) (inputs i) = Zmod.unsigned (N.v27997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27997 s i)) at 1.
  unfold R.v27997, N.v27997.
  unfold R.v6, N.v6.
  rewrite !state_r1250_nr_5F1250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1250_nr_5F1250 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27998 (s : N.State) (i : N.Inputs) :
  R.v27998 (state s) (inputs i) = Zmod.unsigned (N.v27998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27998 s i)) at 1.
  unfold R.v27998, N.v27998.
  unfold R.v6, N.v6.
  rewrite !state_r1249_nr_5F1249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1249_nr_5F1249 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27999 (s : N.State) (i : N.Inputs) :
  R.v27999 (state s) (inputs i) = Zmod.unsigned (N.v27999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27999 s i)) at 1.
  unfold R.v27999, N.v27999.
  rewrite ?node_27997.
  rewrite ?node_27998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
