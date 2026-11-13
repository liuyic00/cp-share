(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes005.
Lemma node_6000 (s : N.State) (i : N.Inputs) :
  R.v6000 (state s) (inputs i) = Zmod.unsigned (N.v6000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6000 s i)) at 1.
  unfold R.v6000, N.v6000.
  rewrite ?node_5999.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2323_nr_5F2354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2323_nr_5F2354 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6001 (s : N.State) (i : N.Inputs) :
  R.v6001 (state s) (inputs i) = Zmod.unsigned (N.v6001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6001 s i)) at 1.
  unfold R.v6001, N.v6001.
  rewrite ?node_5933.
  rewrite ?node_5934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6002 (s : N.State) (i : N.Inputs) :
  R.v6002 (state s) (inputs i) = Zmod.unsigned (N.v6002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6002 s i)) at 1.
  unfold R.v6002, N.v6002.
  rewrite ?node_6001.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2324_nr_5F2355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2324_nr_5F2355 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6003 (s : N.State) (i : N.Inputs) :
  R.v6003 (state s) (inputs i) = Zmod.unsigned (N.v6003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6003 s i)) at 1.
  unfold R.v6003, N.v6003.
  rewrite !state_r208_nr_5F208.
  rewrite !state_r209_nr_5F209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r208_nr_5F208 s)).
  rewrite ?(bits.mod_to_Z (N.r209_nr_5F209 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6004 (s : N.State) (i : N.Inputs) :
  R.v6004 (state s) (inputs i) = Zmod.unsigned (N.v6004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6004 s i)) at 1.
  unfold R.v6004, N.v6004.
  rewrite ?node_6003.
  rewrite !state_r210_nr_5F210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r210_nr_5F210 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6005 (s : N.State) (i : N.Inputs) :
  R.v6005 (state s) (inputs i) = Zmod.unsigned (N.v6005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6005 s i)) at 1.
  unfold R.v6005, N.v6005.
  rewrite ?node_6004.
  rewrite !state_r211_nr_5F211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r211_nr_5F211 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6006 (s : N.State) (i : N.Inputs) :
  R.v6006 (state s) (inputs i) = Zmod.unsigned (N.v6006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6006 s i)) at 1.
  unfold R.v6006, N.v6006.
  rewrite !state_r194_nr_5F194.
  rewrite !state_r195_nr_5F195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r194_nr_5F194 s)).
  rewrite ?(bits.mod_to_Z (N.r195_nr_5F195 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6007 (s : N.State) (i : N.Inputs) :
  R.v6007 (state s) (inputs i) = Zmod.unsigned (N.v6007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6007 s i)) at 1.
  unfold R.v6007, N.v6007.
  rewrite ?node_5939.
  rewrite !state_r196_nr_5F196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r196_nr_5F196 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6008 (s : N.State) (i : N.Inputs) :
  R.v6008 (state s) (inputs i) = Zmod.unsigned (N.v6008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6008 s i)) at 1.
  unfold R.v6008, N.v6008.
  rewrite ?node_6006.
  rewrite ?node_6007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6009 (s : N.State) (i : N.Inputs) :
  R.v6009 (state s) (inputs i) = Zmod.unsigned (N.v6009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6009 s i)) at 1.
  unfold R.v6009, N.v6009.
  rewrite ?node_6005.
  rewrite ?node_6008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6010 (s : N.State) (i : N.Inputs) :
  R.v6010 (state s) (inputs i) = Zmod.unsigned (N.v6010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6010 s i)) at 1.
  unfold R.v6010, N.v6010.
  rewrite !state_r212_nr_5F212.
  rewrite !state_r213_nr_5F213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r212_nr_5F212 s)).
  rewrite ?(bits.mod_to_Z (N.r213_nr_5F213 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6011 (s : N.State) (i : N.Inputs) :
  R.v6011 (state s) (inputs i) = Zmod.unsigned (N.v6011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6011 s i)) at 1.
  unfold R.v6011, N.v6011.
  rewrite ?node_6010.
  rewrite !state_r214_nr_5F214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r214_nr_5F214 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6012 (s : N.State) (i : N.Inputs) :
  R.v6012 (state s) (inputs i) = Zmod.unsigned (N.v6012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6012 s i)) at 1.
  unfold R.v6012, N.v6012.
  rewrite ?node_6011.
  rewrite !state_r215_nr_5F215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r215_nr_5F215 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6013 (s : N.State) (i : N.Inputs) :
  R.v6013 (state s) (inputs i) = Zmod.unsigned (N.v6013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6013 s i)) at 1.
  unfold R.v6013, N.v6013.
  rewrite !state_r198_nr_5F198.
  rewrite !state_r199_nr_5F199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r198_nr_5F198 s)).
  rewrite ?(bits.mod_to_Z (N.r199_nr_5F199 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6014 (s : N.State) (i : N.Inputs) :
  R.v6014 (state s) (inputs i) = Zmod.unsigned (N.v6014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6014 s i)) at 1.
  unfold R.v6014, N.v6014.
  rewrite ?node_5946.
  rewrite !state_r200_nr_5F200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r200_nr_5F200 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6015 (s : N.State) (i : N.Inputs) :
  R.v6015 (state s) (inputs i) = Zmod.unsigned (N.v6015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6015 s i)) at 1.
  unfold R.v6015, N.v6015.
  rewrite ?node_6013.
  rewrite ?node_6014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6016 (s : N.State) (i : N.Inputs) :
  R.v6016 (state s) (inputs i) = Zmod.unsigned (N.v6016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6016 s i)) at 1.
  unfold R.v6016, N.v6016.
  rewrite ?node_6012.
  rewrite ?node_6015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6017 (s : N.State) (i : N.Inputs) :
  R.v6017 (state s) (inputs i) = Zmod.unsigned (N.v6017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6017 s i)) at 1.
  unfold R.v6017, N.v6017.
  rewrite ?node_6009.
  rewrite ?node_6016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6018 (s : N.State) (i : N.Inputs) :
  R.v6018 (state s) (inputs i) = Zmod.unsigned (N.v6018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6018 s i)) at 1.
  unfold R.v6018, N.v6018.
  rewrite !state_r216_nr_5F216.
  rewrite !state_r217_nr_5F217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r216_nr_5F216 s)).
  rewrite ?(bits.mod_to_Z (N.r217_nr_5F217 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6019 (s : N.State) (i : N.Inputs) :
  R.v6019 (state s) (inputs i) = Zmod.unsigned (N.v6019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6019 s i)) at 1.
  unfold R.v6019, N.v6019.
  rewrite ?node_6018.
  rewrite !state_r218_nr_5F218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r218_nr_5F218 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6020 (s : N.State) (i : N.Inputs) :
  R.v6020 (state s) (inputs i) = Zmod.unsigned (N.v6020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6020 s i)) at 1.
  unfold R.v6020, N.v6020.
  rewrite ?node_6019.
  rewrite !state_r219_nr_5F219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r219_nr_5F219 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6021 (s : N.State) (i : N.Inputs) :
  R.v6021 (state s) (inputs i) = Zmod.unsigned (N.v6021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6021 s i)) at 1.
  unfold R.v6021, N.v6021.
  rewrite !state_r202_nr_5F202.
  rewrite !state_r203_nr_5F203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r202_nr_5F202 s)).
  rewrite ?(bits.mod_to_Z (N.r203_nr_5F203 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6022 (s : N.State) (i : N.Inputs) :
  R.v6022 (state s) (inputs i) = Zmod.unsigned (N.v6022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6022 s i)) at 1.
  unfold R.v6022, N.v6022.
  rewrite ?node_5954.
  rewrite !state_r204_nr_5F204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r204_nr_5F204 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6023 (s : N.State) (i : N.Inputs) :
  R.v6023 (state s) (inputs i) = Zmod.unsigned (N.v6023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6023 s i)) at 1.
  unfold R.v6023, N.v6023.
  rewrite ?node_6021.
  rewrite ?node_6022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6024 (s : N.State) (i : N.Inputs) :
  R.v6024 (state s) (inputs i) = Zmod.unsigned (N.v6024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6024 s i)) at 1.
  unfold R.v6024, N.v6024.
  rewrite ?node_6020.
  rewrite ?node_6023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6025 (s : N.State) (i : N.Inputs) :
  R.v6025 (state s) (inputs i) = Zmod.unsigned (N.v6025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6025 s i)) at 1.
  unfold R.v6025, N.v6025.
  rewrite ?node_6017.
  rewrite ?node_6024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6026 (s : N.State) (i : N.Inputs) :
  R.v6026 (state s) (inputs i) = Zmod.unsigned (N.v6026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6026 s i)) at 1.
  unfold R.v6026, N.v6026.
  rewrite !state_r220_nr_5F220.
  rewrite !state_r221_nr_5F221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r220_nr_5F220 s)).
  rewrite ?(bits.mod_to_Z (N.r221_nr_5F221 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6027 (s : N.State) (i : N.Inputs) :
  R.v6027 (state s) (inputs i) = Zmod.unsigned (N.v6027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6027 s i)) at 1.
  unfold R.v6027, N.v6027.
  rewrite ?node_6026.
  rewrite !state_r222_nr_5F222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r222_nr_5F222 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6028 (s : N.State) (i : N.Inputs) :
  R.v6028 (state s) (inputs i) = Zmod.unsigned (N.v6028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6028 s i)) at 1.
  unfold R.v6028, N.v6028.
  rewrite ?node_6025.
  rewrite ?node_6027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6029 (s : N.State) (i : N.Inputs) :
  R.v6029 (state s) (inputs i) = Zmod.unsigned (N.v6029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6029 s i)) at 1.
  unfold R.v6029, N.v6029.
  rewrite ?node_5945.
  rewrite ?node_5952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6030 (s : N.State) (i : N.Inputs) :
  R.v6030 (state s) (inputs i) = Zmod.unsigned (N.v6030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6030 s i)) at 1.
  unfold R.v6030, N.v6030.
  rewrite ?node_5953.
  rewrite ?node_5960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6031 (s : N.State) (i : N.Inputs) :
  R.v6031 (state s) (inputs i) = Zmod.unsigned (N.v6031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6031 s i)) at 1.
  unfold R.v6031, N.v6031.
  rewrite ?node_6029.
  rewrite ?node_6030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6032 (s : N.State) (i : N.Inputs) :
  R.v6032 (state s) (inputs i) = Zmod.unsigned (N.v6032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6032 s i)) at 1.
  unfold R.v6032, N.v6032.
  rewrite ?node_6028.
  rewrite ?node_6031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6033 (s : N.State) (i : N.Inputs) :
  R.v6033 (state s) (inputs i) = Zmod.unsigned (N.v6033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6033 s i)) at 1.
  unfold R.v6033, N.v6033.
  rewrite ?node_5940.
  rewrite !state_r197_nr_5F197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r197_nr_5F197 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6034 (s : N.State) (i : N.Inputs) :
  R.v6034 (state s) (inputs i) = Zmod.unsigned (N.v6034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6034 s i)) at 1.
  unfold R.v6034, N.v6034.
  rewrite ?node_5941.
  rewrite ?node_5944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6035 (s : N.State) (i : N.Inputs) :
  R.v6035 (state s) (inputs i) = Zmod.unsigned (N.v6035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6035 s i)) at 1.
  unfold R.v6035, N.v6035.
  rewrite ?node_6033.
  rewrite ?node_6034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6036 (s : N.State) (i : N.Inputs) :
  R.v6036 (state s) (inputs i) = Zmod.unsigned (N.v6036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6036 s i)) at 1.
  unfold R.v6036, N.v6036.
  rewrite ?node_5947.
  rewrite !state_r201_nr_5F201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r201_nr_5F201 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6037 (s : N.State) (i : N.Inputs) :
  R.v6037 (state s) (inputs i) = Zmod.unsigned (N.v6037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6037 s i)) at 1.
  unfold R.v6037, N.v6037.
  rewrite ?node_5948.
  rewrite ?node_5951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6038 (s : N.State) (i : N.Inputs) :
  R.v6038 (state s) (inputs i) = Zmod.unsigned (N.v6038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6038 s i)) at 1.
  unfold R.v6038, N.v6038.
  rewrite ?node_6036.
  rewrite ?node_6037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6039 (s : N.State) (i : N.Inputs) :
  R.v6039 (state s) (inputs i) = Zmod.unsigned (N.v6039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6039 s i)) at 1.
  unfold R.v6039, N.v6039.
  rewrite ?node_6035.
  rewrite ?node_6038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6040 (s : N.State) (i : N.Inputs) :
  R.v6040 (state s) (inputs i) = Zmod.unsigned (N.v6040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6040 s i)) at 1.
  unfold R.v6040, N.v6040.
  rewrite ?node_5955.
  rewrite !state_r205_nr_5F205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r205_nr_5F205 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6041 (s : N.State) (i : N.Inputs) :
  R.v6041 (state s) (inputs i) = Zmod.unsigned (N.v6041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6041 s i)) at 1.
  unfold R.v6041, N.v6041.
  rewrite ?node_5956.
  rewrite ?node_5959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6042 (s : N.State) (i : N.Inputs) :
  R.v6042 (state s) (inputs i) = Zmod.unsigned (N.v6042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6042 s i)) at 1.
  unfold R.v6042, N.v6042.
  rewrite ?node_6040.
  rewrite ?node_6041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6043 (s : N.State) (i : N.Inputs) :
  R.v6043 (state s) (inputs i) = Zmod.unsigned (N.v6043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6043 s i)) at 1.
  unfold R.v6043, N.v6043.
  rewrite ?node_6039.
  rewrite ?node_6042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6044 (s : N.State) (i : N.Inputs) :
  R.v6044 (state s) (inputs i) = Zmod.unsigned (N.v6044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6044 s i)) at 1.
  unfold R.v6044, N.v6044.
  rewrite !state_r206_nr_5F206.
  rewrite !state_r207_nr_5F207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r206_nr_5F206 s)).
  rewrite ?(bits.mod_to_Z (N.r207_nr_5F207 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6045 (s : N.State) (i : N.Inputs) :
  R.v6045 (state s) (inputs i) = Zmod.unsigned (N.v6045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6045 s i)) at 1.
  unfold R.v6045, N.v6045.
  rewrite ?node_6043.
  rewrite ?node_6044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6046 (s : N.State) (i : N.Inputs) :
  R.v6046 (state s) (inputs i) = Zmod.unsigned (N.v6046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6046 s i)) at 1.
  unfold R.v6046, N.v6046.
  rewrite ?node_5970.
  rewrite ?node_5973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6047 (s : N.State) (i : N.Inputs) :
  R.v6047 (state s) (inputs i) = Zmod.unsigned (N.v6047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6047 s i)) at 1.
  unfold R.v6047, N.v6047.
  rewrite ?node_5974.
  rewrite ?node_5977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6048 (s : N.State) (i : N.Inputs) :
  R.v6048 (state s) (inputs i) = Zmod.unsigned (N.v6048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6048 s i)) at 1.
  unfold R.v6048, N.v6048.
  rewrite ?node_6046.
  rewrite ?node_6047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6049 (s : N.State) (i : N.Inputs) :
  R.v6049 (state s) (inputs i) = Zmod.unsigned (N.v6049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6049 s i)) at 1.
  unfold R.v6049, N.v6049.
  rewrite ?node_6045.
  rewrite ?node_6048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6050 (s : N.State) (i : N.Inputs) :
  R.v6050 (state s) (inputs i) = Zmod.unsigned (N.v6050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6050 s i)) at 1.
  unfold R.v6050, N.v6050.
  rewrite ?node_6032.
  rewrite ?node_6049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6051 (s : N.State) (i : N.Inputs) :
  R.v6051 (state s) (inputs i) = Zmod.unsigned (N.v6051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6051 s i)) at 1.
  unfold R.v6051, N.v6051.
  rewrite ?node_5961.
  rewrite ?node_5962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6052 (s : N.State) (i : N.Inputs) :
  R.v6052 (state s) (inputs i) = Zmod.unsigned (N.v6052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6052 s i)) at 1.
  unfold R.v6052, N.v6052.
  rewrite ?node_5963.
  rewrite ?node_5966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6053 (s : N.State) (i : N.Inputs) :
  R.v6053 (state s) (inputs i) = Zmod.unsigned (N.v6053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6053 s i)) at 1.
  unfold R.v6053, N.v6053.
  rewrite ?node_6051.
  rewrite ?node_6052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6054 (s : N.State) (i : N.Inputs) :
  R.v6054 (state s) (inputs i) = Zmod.unsigned (N.v6054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6054 s i)) at 1.
  unfold R.v6054, N.v6054.
  rewrite ?node_6050.
  rewrite ?node_6053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6055 (s : N.State) (i : N.Inputs) :
  R.v6055 (state s) (inputs i) = Zmod.unsigned (N.v6055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6055 s i)) at 1.
  unfold R.v6055, N.v6055.
  rewrite ?node_5978.
  rewrite ?node_5979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6056 (s : N.State) (i : N.Inputs) :
  R.v6056 (state s) (inputs i) = Zmod.unsigned (N.v6056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6056 s i)) at 1.
  unfold R.v6056, N.v6056.
  rewrite ?node_6054.
  rewrite ?node_6055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6057 (s : N.State) (i : N.Inputs) :
  R.v6057 (state s) (inputs i) = Zmod.unsigned (N.v6057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6057 s i)) at 1.
  unfold R.v6057, N.v6057.
  rewrite ?node_5967.
  rewrite ?node_5980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6058 (s : N.State) (i : N.Inputs) :
  R.v6058 (state s) (inputs i) = Zmod.unsigned (N.v6058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6058 s i)) at 1.
  unfold R.v6058, N.v6058.
  rewrite ?node_5981.
  rewrite ?node_5984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6059 (s : N.State) (i : N.Inputs) :
  R.v6059 (state s) (inputs i) = Zmod.unsigned (N.v6059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6059 s i)) at 1.
  unfold R.v6059, N.v6059.
  rewrite ?node_6057.
  rewrite ?node_6058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6060 (s : N.State) (i : N.Inputs) :
  R.v6060 (state s) (inputs i) = Zmod.unsigned (N.v6060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6060 s i)) at 1.
  unfold R.v6060, N.v6060.
  rewrite ?node_6056.
  rewrite ?node_6059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6061 (s : N.State) (i : N.Inputs) :
  R.v6061 (state s) (inputs i) = Zmod.unsigned (N.v6061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6061 s i)) at 1.
  unfold R.v6061, N.v6061.
  rewrite ?node_5985.
  rewrite ?node_5988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6062 (s : N.State) (i : N.Inputs) :
  R.v6062 (state s) (inputs i) = Zmod.unsigned (N.v6062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6062 s i)) at 1.
  unfold R.v6062, N.v6062.
  rewrite ?node_5989.
  rewrite ?node_5992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6063 (s : N.State) (i : N.Inputs) :
  R.v6063 (state s) (inputs i) = Zmod.unsigned (N.v6063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6063 s i)) at 1.
  unfold R.v6063, N.v6063.
  rewrite ?node_6061.
  rewrite ?node_6062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6064 (s : N.State) (i : N.Inputs) :
  R.v6064 (state s) (inputs i) = Zmod.unsigned (N.v6064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6064 s i)) at 1.
  unfold R.v6064, N.v6064.
  rewrite ?node_6060.
  rewrite ?node_6063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6065 (s : N.State) (i : N.Inputs) :
  R.v6065 (state s) (inputs i) = Zmod.unsigned (N.v6065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6065 s i)) at 1.
  unfold R.v6065, N.v6065.
  rewrite ?node_5993.
  rewrite ?node_5996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6066 (s : N.State) (i : N.Inputs) :
  R.v6066 (state s) (inputs i) = Zmod.unsigned (N.v6066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6066 s i)) at 1.
  unfold R.v6066, N.v6066.
  rewrite ?node_6064.
  rewrite ?node_6065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6067 (s : N.State) (i : N.Inputs) :
  R.v6067 (state s) (inputs i) = Zmod.unsigned (N.v6067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6067 s i)) at 1.
  unfold R.v6067, N.v6067.
  rewrite ?node_6066.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2325_nr_5F2356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2325_nr_5F2356 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6068 (s : N.State) (i : N.Inputs) :
  R.v6068 (state s) (inputs i) = Zmod.unsigned (N.v6068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6068 s i)) at 1.
  unfold R.v6068, N.v6068.
  rewrite ?node_5997.
  rewrite ?node_5998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6069 (s : N.State) (i : N.Inputs) :
  R.v6069 (state s) (inputs i) = Zmod.unsigned (N.v6069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6069 s i)) at 1.
  unfold R.v6069, N.v6069.
  rewrite ?node_6068.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2326_nr_5F2357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2326_nr_5F2357 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6070 (s : N.State) (i : N.Inputs) :
  R.v6070 (state s) (inputs i) = Zmod.unsigned (N.v6070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6070 s i)) at 1.
  unfold R.v6070, N.v6070.
  rewrite !state_r223_nr_5F223.
  rewrite !state_r224_nr_5F224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r223_nr_5F223 s)).
  rewrite ?(bits.mod_to_Z (N.r224_nr_5F224 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6071 (s : N.State) (i : N.Inputs) :
  R.v6071 (state s) (inputs i) = Zmod.unsigned (N.v6071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6071 s i)) at 1.
  unfold R.v6071, N.v6071.
  rewrite ?node_6070.
  rewrite !state_r225_nr_5F225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r225_nr_5F225 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6072 (s : N.State) (i : N.Inputs) :
  R.v6072 (state s) (inputs i) = Zmod.unsigned (N.v6072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6072 s i)) at 1.
  unfold R.v6072, N.v6072.
  rewrite ?node_6071.
  rewrite !state_r226_nr_5F226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r226_nr_5F226 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6073 (s : N.State) (i : N.Inputs) :
  R.v6073 (state s) (inputs i) = Zmod.unsigned (N.v6073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6073 s i)) at 1.
  unfold R.v6073, N.v6073.
  rewrite !state_r208_nr_5F208.
  rewrite !state_r209_nr_5F209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r208_nr_5F208 s)).
  rewrite ?(bits.mod_to_Z (N.r209_nr_5F209 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6074 (s : N.State) (i : N.Inputs) :
  R.v6074 (state s) (inputs i) = Zmod.unsigned (N.v6074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6074 s i)) at 1.
  unfold R.v6074, N.v6074.
  rewrite ?node_6003.
  rewrite !state_r210_nr_5F210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r210_nr_5F210 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6075 (s : N.State) (i : N.Inputs) :
  R.v6075 (state s) (inputs i) = Zmod.unsigned (N.v6075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6075 s i)) at 1.
  unfold R.v6075, N.v6075.
  rewrite ?node_6073.
  rewrite ?node_6074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6076 (s : N.State) (i : N.Inputs) :
  R.v6076 (state s) (inputs i) = Zmod.unsigned (N.v6076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6076 s i)) at 1.
  unfold R.v6076, N.v6076.
  rewrite ?node_6072.
  rewrite ?node_6075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6077 (s : N.State) (i : N.Inputs) :
  R.v6077 (state s) (inputs i) = Zmod.unsigned (N.v6077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6077 s i)) at 1.
  unfold R.v6077, N.v6077.
  rewrite !state_r227_nr_5F227.
  rewrite !state_r228_nr_5F228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r227_nr_5F227 s)).
  rewrite ?(bits.mod_to_Z (N.r228_nr_5F228 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6078 (s : N.State) (i : N.Inputs) :
  R.v6078 (state s) (inputs i) = Zmod.unsigned (N.v6078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6078 s i)) at 1.
  unfold R.v6078, N.v6078.
  rewrite ?node_6077.
  rewrite !state_r229_nr_5F229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r229_nr_5F229 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6079 (s : N.State) (i : N.Inputs) :
  R.v6079 (state s) (inputs i) = Zmod.unsigned (N.v6079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6079 s i)) at 1.
  unfold R.v6079, N.v6079.
  rewrite ?node_6078.
  rewrite !state_r230_nr_5F230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r230_nr_5F230 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6080 (s : N.State) (i : N.Inputs) :
  R.v6080 (state s) (inputs i) = Zmod.unsigned (N.v6080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6080 s i)) at 1.
  unfold R.v6080, N.v6080.
  rewrite !state_r212_nr_5F212.
  rewrite !state_r213_nr_5F213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r212_nr_5F212 s)).
  rewrite ?(bits.mod_to_Z (N.r213_nr_5F213 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6081 (s : N.State) (i : N.Inputs) :
  R.v6081 (state s) (inputs i) = Zmod.unsigned (N.v6081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6081 s i)) at 1.
  unfold R.v6081, N.v6081.
  rewrite ?node_6010.
  rewrite !state_r214_nr_5F214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r214_nr_5F214 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6082 (s : N.State) (i : N.Inputs) :
  R.v6082 (state s) (inputs i) = Zmod.unsigned (N.v6082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6082 s i)) at 1.
  unfold R.v6082, N.v6082.
  rewrite ?node_6080.
  rewrite ?node_6081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6083 (s : N.State) (i : N.Inputs) :
  R.v6083 (state s) (inputs i) = Zmod.unsigned (N.v6083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6083 s i)) at 1.
  unfold R.v6083, N.v6083.
  rewrite ?node_6079.
  rewrite ?node_6082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6084 (s : N.State) (i : N.Inputs) :
  R.v6084 (state s) (inputs i) = Zmod.unsigned (N.v6084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6084 s i)) at 1.
  unfold R.v6084, N.v6084.
  rewrite ?node_6076.
  rewrite ?node_6083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6085 (s : N.State) (i : N.Inputs) :
  R.v6085 (state s) (inputs i) = Zmod.unsigned (N.v6085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6085 s i)) at 1.
  unfold R.v6085, N.v6085.
  rewrite !state_r231_nr_5F231.
  rewrite !state_r232_nr_5F232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r231_nr_5F231 s)).
  rewrite ?(bits.mod_to_Z (N.r232_nr_5F232 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6086 (s : N.State) (i : N.Inputs) :
  R.v6086 (state s) (inputs i) = Zmod.unsigned (N.v6086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6086 s i)) at 1.
  unfold R.v6086, N.v6086.
  rewrite ?node_6085.
  rewrite !state_r233_nr_5F233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r233_nr_5F233 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6087 (s : N.State) (i : N.Inputs) :
  R.v6087 (state s) (inputs i) = Zmod.unsigned (N.v6087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6087 s i)) at 1.
  unfold R.v6087, N.v6087.
  rewrite ?node_6086.
  rewrite !state_r234_nr_5F234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r234_nr_5F234 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6088 (s : N.State) (i : N.Inputs) :
  R.v6088 (state s) (inputs i) = Zmod.unsigned (N.v6088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6088 s i)) at 1.
  unfold R.v6088, N.v6088.
  rewrite !state_r216_nr_5F216.
  rewrite !state_r217_nr_5F217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r216_nr_5F216 s)).
  rewrite ?(bits.mod_to_Z (N.r217_nr_5F217 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6089 (s : N.State) (i : N.Inputs) :
  R.v6089 (state s) (inputs i) = Zmod.unsigned (N.v6089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6089 s i)) at 1.
  unfold R.v6089, N.v6089.
  rewrite ?node_6018.
  rewrite !state_r218_nr_5F218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r218_nr_5F218 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6090 (s : N.State) (i : N.Inputs) :
  R.v6090 (state s) (inputs i) = Zmod.unsigned (N.v6090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6090 s i)) at 1.
  unfold R.v6090, N.v6090.
  rewrite ?node_6088.
  rewrite ?node_6089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6091 (s : N.State) (i : N.Inputs) :
  R.v6091 (state s) (inputs i) = Zmod.unsigned (N.v6091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6091 s i)) at 1.
  unfold R.v6091, N.v6091.
  rewrite ?node_6087.
  rewrite ?node_6090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6092 (s : N.State) (i : N.Inputs) :
  R.v6092 (state s) (inputs i) = Zmod.unsigned (N.v6092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6092 s i)) at 1.
  unfold R.v6092, N.v6092.
  rewrite ?node_6084.
  rewrite ?node_6091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6093 (s : N.State) (i : N.Inputs) :
  R.v6093 (state s) (inputs i) = Zmod.unsigned (N.v6093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6093 s i)) at 1.
  unfold R.v6093, N.v6093.
  rewrite !state_r235_nr_5F235.
  rewrite !state_r236_nr_5F236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r235_nr_5F235 s)).
  rewrite ?(bits.mod_to_Z (N.r236_nr_5F236 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6094 (s : N.State) (i : N.Inputs) :
  R.v6094 (state s) (inputs i) = Zmod.unsigned (N.v6094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6094 s i)) at 1.
  unfold R.v6094, N.v6094.
  rewrite ?node_6093.
  rewrite !state_r237_nr_5F237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r237_nr_5F237 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6095 (s : N.State) (i : N.Inputs) :
  R.v6095 (state s) (inputs i) = Zmod.unsigned (N.v6095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6095 s i)) at 1.
  unfold R.v6095, N.v6095.
  rewrite ?node_6092.
  rewrite ?node_6094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6096 (s : N.State) (i : N.Inputs) :
  R.v6096 (state s) (inputs i) = Zmod.unsigned (N.v6096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6096 s i)) at 1.
  unfold R.v6096, N.v6096.
  rewrite ?node_6009.
  rewrite ?node_6016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6097 (s : N.State) (i : N.Inputs) :
  R.v6097 (state s) (inputs i) = Zmod.unsigned (N.v6097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6097 s i)) at 1.
  unfold R.v6097, N.v6097.
  rewrite ?node_6017.
  rewrite ?node_6024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6098 (s : N.State) (i : N.Inputs) :
  R.v6098 (state s) (inputs i) = Zmod.unsigned (N.v6098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6098 s i)) at 1.
  unfold R.v6098, N.v6098.
  rewrite ?node_6096.
  rewrite ?node_6097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6099 (s : N.State) (i : N.Inputs) :
  R.v6099 (state s) (inputs i) = Zmod.unsigned (N.v6099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6099 s i)) at 1.
  unfold R.v6099, N.v6099.
  rewrite ?node_6095.
  rewrite ?node_6098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6100 (s : N.State) (i : N.Inputs) :
  R.v6100 (state s) (inputs i) = Zmod.unsigned (N.v6100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6100 s i)) at 1.
  unfold R.v6100, N.v6100.
  rewrite ?node_6004.
  rewrite !state_r211_nr_5F211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r211_nr_5F211 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6101 (s : N.State) (i : N.Inputs) :
  R.v6101 (state s) (inputs i) = Zmod.unsigned (N.v6101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6101 s i)) at 1.
  unfold R.v6101, N.v6101.
  rewrite ?node_6005.
  rewrite ?node_6008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6102 (s : N.State) (i : N.Inputs) :
  R.v6102 (state s) (inputs i) = Zmod.unsigned (N.v6102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6102 s i)) at 1.
  unfold R.v6102, N.v6102.
  rewrite ?node_6100.
  rewrite ?node_6101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6103 (s : N.State) (i : N.Inputs) :
  R.v6103 (state s) (inputs i) = Zmod.unsigned (N.v6103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6103 s i)) at 1.
  unfold R.v6103, N.v6103.
  rewrite ?node_6011.
  rewrite !state_r215_nr_5F215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r215_nr_5F215 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6104 (s : N.State) (i : N.Inputs) :
  R.v6104 (state s) (inputs i) = Zmod.unsigned (N.v6104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6104 s i)) at 1.
  unfold R.v6104, N.v6104.
  rewrite ?node_6012.
  rewrite ?node_6015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6105 (s : N.State) (i : N.Inputs) :
  R.v6105 (state s) (inputs i) = Zmod.unsigned (N.v6105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6105 s i)) at 1.
  unfold R.v6105, N.v6105.
  rewrite ?node_6103.
  rewrite ?node_6104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6106 (s : N.State) (i : N.Inputs) :
  R.v6106 (state s) (inputs i) = Zmod.unsigned (N.v6106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6106 s i)) at 1.
  unfold R.v6106, N.v6106.
  rewrite ?node_6102.
  rewrite ?node_6105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6107 (s : N.State) (i : N.Inputs) :
  R.v6107 (state s) (inputs i) = Zmod.unsigned (N.v6107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6107 s i)) at 1.
  unfold R.v6107, N.v6107.
  rewrite ?node_6019.
  rewrite !state_r219_nr_5F219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r219_nr_5F219 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6108 (s : N.State) (i : N.Inputs) :
  R.v6108 (state s) (inputs i) = Zmod.unsigned (N.v6108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6108 s i)) at 1.
  unfold R.v6108, N.v6108.
  rewrite ?node_6020.
  rewrite ?node_6023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6109 (s : N.State) (i : N.Inputs) :
  R.v6109 (state s) (inputs i) = Zmod.unsigned (N.v6109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6109 s i)) at 1.
  unfold R.v6109, N.v6109.
  rewrite ?node_6107.
  rewrite ?node_6108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6110 (s : N.State) (i : N.Inputs) :
  R.v6110 (state s) (inputs i) = Zmod.unsigned (N.v6110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6110 s i)) at 1.
  unfold R.v6110, N.v6110.
  rewrite ?node_6106.
  rewrite ?node_6109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6111 (s : N.State) (i : N.Inputs) :
  R.v6111 (state s) (inputs i) = Zmod.unsigned (N.v6111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6111 s i)) at 1.
  unfold R.v6111, N.v6111.
  rewrite !state_r220_nr_5F220.
  rewrite !state_r221_nr_5F221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r220_nr_5F220 s)).
  rewrite ?(bits.mod_to_Z (N.r221_nr_5F221 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6112 (s : N.State) (i : N.Inputs) :
  R.v6112 (state s) (inputs i) = Zmod.unsigned (N.v6112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6112 s i)) at 1.
  unfold R.v6112, N.v6112.
  rewrite ?node_6026.
  rewrite !state_r222_nr_5F222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r222_nr_5F222 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6113 (s : N.State) (i : N.Inputs) :
  R.v6113 (state s) (inputs i) = Zmod.unsigned (N.v6113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6113 s i)) at 1.
  unfold R.v6113, N.v6113.
  rewrite ?node_6111.
  rewrite ?node_6112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6114 (s : N.State) (i : N.Inputs) :
  R.v6114 (state s) (inputs i) = Zmod.unsigned (N.v6114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6114 s i)) at 1.
  unfold R.v6114, N.v6114.
  rewrite ?node_6110.
  rewrite ?node_6113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6115 (s : N.State) (i : N.Inputs) :
  R.v6115 (state s) (inputs i) = Zmod.unsigned (N.v6115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6115 s i)) at 1.
  unfold R.v6115, N.v6115.
  rewrite ?node_6035.
  rewrite ?node_6038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6116 (s : N.State) (i : N.Inputs) :
  R.v6116 (state s) (inputs i) = Zmod.unsigned (N.v6116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6116 s i)) at 1.
  unfold R.v6116, N.v6116.
  rewrite ?node_6039.
  rewrite ?node_6042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6117 (s : N.State) (i : N.Inputs) :
  R.v6117 (state s) (inputs i) = Zmod.unsigned (N.v6117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6117 s i)) at 1.
  unfold R.v6117, N.v6117.
  rewrite ?node_6115.
  rewrite ?node_6116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6118 (s : N.State) (i : N.Inputs) :
  R.v6118 (state s) (inputs i) = Zmod.unsigned (N.v6118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6118 s i)) at 1.
  unfold R.v6118, N.v6118.
  rewrite ?node_6114.
  rewrite ?node_6117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6119 (s : N.State) (i : N.Inputs) :
  R.v6119 (state s) (inputs i) = Zmod.unsigned (N.v6119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6119 s i)) at 1.
  unfold R.v6119, N.v6119.
  rewrite ?node_6099.
  rewrite ?node_6118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6120 (s : N.State) (i : N.Inputs) :
  R.v6120 (state s) (inputs i) = Zmod.unsigned (N.v6120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6120 s i)) at 1.
  unfold R.v6120, N.v6120.
  rewrite ?node_6025.
  rewrite ?node_6027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6121 (s : N.State) (i : N.Inputs) :
  R.v6121 (state s) (inputs i) = Zmod.unsigned (N.v6121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6121 s i)) at 1.
  unfold R.v6121, N.v6121.
  rewrite ?node_6028.
  rewrite ?node_6031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6122 (s : N.State) (i : N.Inputs) :
  R.v6122 (state s) (inputs i) = Zmod.unsigned (N.v6122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6122 s i)) at 1.
  unfold R.v6122, N.v6122.
  rewrite ?node_6120.
  rewrite ?node_6121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6123 (s : N.State) (i : N.Inputs) :
  R.v6123 (state s) (inputs i) = Zmod.unsigned (N.v6123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6123 s i)) at 1.
  unfold R.v6123, N.v6123.
  rewrite ?node_6119.
  rewrite ?node_6122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6124 (s : N.State) (i : N.Inputs) :
  R.v6124 (state s) (inputs i) = Zmod.unsigned (N.v6124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6124 s i)) at 1.
  unfold R.v6124, N.v6124.
  rewrite ?node_6043.
  rewrite ?node_6044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6125 (s : N.State) (i : N.Inputs) :
  R.v6125 (state s) (inputs i) = Zmod.unsigned (N.v6125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6125 s i)) at 1.
  unfold R.v6125, N.v6125.
  rewrite ?node_6045.
  rewrite ?node_6048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6126 (s : N.State) (i : N.Inputs) :
  R.v6126 (state s) (inputs i) = Zmod.unsigned (N.v6126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6126 s i)) at 1.
  unfold R.v6126, N.v6126.
  rewrite ?node_6124.
  rewrite ?node_6125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6127 (s : N.State) (i : N.Inputs) :
  R.v6127 (state s) (inputs i) = Zmod.unsigned (N.v6127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6127 s i)) at 1.
  unfold R.v6127, N.v6127.
  rewrite ?node_6123.
  rewrite ?node_6126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6128 (s : N.State) (i : N.Inputs) :
  R.v6128 (state s) (inputs i) = Zmod.unsigned (N.v6128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6128 s i)) at 1.
  unfold R.v6128, N.v6128.
  rewrite ?node_6032.
  rewrite ?node_6049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6129 (s : N.State) (i : N.Inputs) :
  R.v6129 (state s) (inputs i) = Zmod.unsigned (N.v6129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6129 s i)) at 1.
  unfold R.v6129, N.v6129.
  rewrite ?node_6050.
  rewrite ?node_6053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6130 (s : N.State) (i : N.Inputs) :
  R.v6130 (state s) (inputs i) = Zmod.unsigned (N.v6130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6130 s i)) at 1.
  unfold R.v6130, N.v6130.
  rewrite ?node_6128.
  rewrite ?node_6129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6131 (s : N.State) (i : N.Inputs) :
  R.v6131 (state s) (inputs i) = Zmod.unsigned (N.v6131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6131 s i)) at 1.
  unfold R.v6131, N.v6131.
  rewrite ?node_6127.
  rewrite ?node_6130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6132 (s : N.State) (i : N.Inputs) :
  R.v6132 (state s) (inputs i) = Zmod.unsigned (N.v6132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6132 s i)) at 1.
  unfold R.v6132, N.v6132.
  rewrite ?node_6054.
  rewrite ?node_6055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6133 (s : N.State) (i : N.Inputs) :
  R.v6133 (state s) (inputs i) = Zmod.unsigned (N.v6133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6133 s i)) at 1.
  unfold R.v6133, N.v6133.
  rewrite ?node_6056.
  rewrite ?node_6059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6134 (s : N.State) (i : N.Inputs) :
  R.v6134 (state s) (inputs i) = Zmod.unsigned (N.v6134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6134 s i)) at 1.
  unfold R.v6134, N.v6134.
  rewrite ?node_6132.
  rewrite ?node_6133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6135 (s : N.State) (i : N.Inputs) :
  R.v6135 (state s) (inputs i) = Zmod.unsigned (N.v6135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6135 s i)) at 1.
  unfold R.v6135, N.v6135.
  rewrite ?node_6131.
  rewrite ?node_6134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6136 (s : N.State) (i : N.Inputs) :
  R.v6136 (state s) (inputs i) = Zmod.unsigned (N.v6136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6136 s i)) at 1.
  unfold R.v6136, N.v6136.
  rewrite ?node_6060.
  rewrite ?node_6063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6137 (s : N.State) (i : N.Inputs) :
  R.v6137 (state s) (inputs i) = Zmod.unsigned (N.v6137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6137 s i)) at 1.
  unfold R.v6137, N.v6137.
  rewrite ?node_6135.
  rewrite ?node_6136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6138 (s : N.State) (i : N.Inputs) :
  R.v6138 (state s) (inputs i) = Zmod.unsigned (N.v6138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6138 s i)) at 1.
  unfold R.v6138, N.v6138.
  rewrite ?node_6137.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2327_nr_5F2358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2327_nr_5F2358 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6139 (s : N.State) (i : N.Inputs) :
  R.v6139 (state s) (inputs i) = Zmod.unsigned (N.v6139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6139 s i)) at 1.
  unfold R.v6139, N.v6139.
  rewrite ?node_6064.
  rewrite ?node_6065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6140 (s : N.State) (i : N.Inputs) :
  R.v6140 (state s) (inputs i) = Zmod.unsigned (N.v6140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6140 s i)) at 1.
  unfold R.v6140, N.v6140.
  rewrite ?node_6139.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2328_nr_5F2359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2328_nr_5F2359 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6141 (s : N.State) (i : N.Inputs) :
  R.v6141 (state s) (inputs i) = Zmod.unsigned (N.v6141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6141 s i)) at 1.
  unfold R.v6141, N.v6141.
  rewrite !state_r238_nr_5F238.
  rewrite !state_r239_nr_5F239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r238_nr_5F238 s)).
  rewrite ?(bits.mod_to_Z (N.r239_nr_5F239 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6142 (s : N.State) (i : N.Inputs) :
  R.v6142 (state s) (inputs i) = Zmod.unsigned (N.v6142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6142 s i)) at 1.
  unfold R.v6142, N.v6142.
  rewrite ?node_6141.
  rewrite !state_r240_nr_5F240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r240_nr_5F240 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6143 (s : N.State) (i : N.Inputs) :
  R.v6143 (state s) (inputs i) = Zmod.unsigned (N.v6143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6143 s i)) at 1.
  unfold R.v6143, N.v6143.
  rewrite ?node_6142.
  rewrite !state_r241_nr_5F241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r241_nr_5F241 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6144 (s : N.State) (i : N.Inputs) :
  R.v6144 (state s) (inputs i) = Zmod.unsigned (N.v6144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6144 s i)) at 1.
  unfold R.v6144, N.v6144.
  rewrite !state_r223_nr_5F223.
  rewrite !state_r224_nr_5F224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r223_nr_5F223 s)).
  rewrite ?(bits.mod_to_Z (N.r224_nr_5F224 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6145 (s : N.State) (i : N.Inputs) :
  R.v6145 (state s) (inputs i) = Zmod.unsigned (N.v6145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6145 s i)) at 1.
  unfold R.v6145, N.v6145.
  rewrite ?node_6070.
  rewrite !state_r225_nr_5F225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r225_nr_5F225 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6146 (s : N.State) (i : N.Inputs) :
  R.v6146 (state s) (inputs i) = Zmod.unsigned (N.v6146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6146 s i)) at 1.
  unfold R.v6146, N.v6146.
  rewrite ?node_6144.
  rewrite ?node_6145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6147 (s : N.State) (i : N.Inputs) :
  R.v6147 (state s) (inputs i) = Zmod.unsigned (N.v6147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6147 s i)) at 1.
  unfold R.v6147, N.v6147.
  rewrite ?node_6143.
  rewrite ?node_6146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6148 (s : N.State) (i : N.Inputs) :
  R.v6148 (state s) (inputs i) = Zmod.unsigned (N.v6148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6148 s i)) at 1.
  unfold R.v6148, N.v6148.
  rewrite !state_r242_nr_5F242.
  rewrite !state_r243_nr_5F243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r242_nr_5F242 s)).
  rewrite ?(bits.mod_to_Z (N.r243_nr_5F243 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6149 (s : N.State) (i : N.Inputs) :
  R.v6149 (state s) (inputs i) = Zmod.unsigned (N.v6149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6149 s i)) at 1.
  unfold R.v6149, N.v6149.
  rewrite ?node_6148.
  rewrite !state_r244_nr_5F244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r244_nr_5F244 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6150 (s : N.State) (i : N.Inputs) :
  R.v6150 (state s) (inputs i) = Zmod.unsigned (N.v6150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6150 s i)) at 1.
  unfold R.v6150, N.v6150.
  rewrite ?node_6149.
  rewrite !state_r245_nr_5F245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r245_nr_5F245 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6151 (s : N.State) (i : N.Inputs) :
  R.v6151 (state s) (inputs i) = Zmod.unsigned (N.v6151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6151 s i)) at 1.
  unfold R.v6151, N.v6151.
  rewrite !state_r227_nr_5F227.
  rewrite !state_r228_nr_5F228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r227_nr_5F227 s)).
  rewrite ?(bits.mod_to_Z (N.r228_nr_5F228 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6152 (s : N.State) (i : N.Inputs) :
  R.v6152 (state s) (inputs i) = Zmod.unsigned (N.v6152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6152 s i)) at 1.
  unfold R.v6152, N.v6152.
  rewrite ?node_6077.
  rewrite !state_r229_nr_5F229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r229_nr_5F229 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6153 (s : N.State) (i : N.Inputs) :
  R.v6153 (state s) (inputs i) = Zmod.unsigned (N.v6153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6153 s i)) at 1.
  unfold R.v6153, N.v6153.
  rewrite ?node_6151.
  rewrite ?node_6152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6154 (s : N.State) (i : N.Inputs) :
  R.v6154 (state s) (inputs i) = Zmod.unsigned (N.v6154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6154 s i)) at 1.
  unfold R.v6154, N.v6154.
  rewrite ?node_6150.
  rewrite ?node_6153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6155 (s : N.State) (i : N.Inputs) :
  R.v6155 (state s) (inputs i) = Zmod.unsigned (N.v6155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6155 s i)) at 1.
  unfold R.v6155, N.v6155.
  rewrite ?node_6147.
  rewrite ?node_6154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6156 (s : N.State) (i : N.Inputs) :
  R.v6156 (state s) (inputs i) = Zmod.unsigned (N.v6156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6156 s i)) at 1.
  unfold R.v6156, N.v6156.
  rewrite !state_r246_nr_5F246.
  rewrite !state_r247_nr_5F247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r246_nr_5F246 s)).
  rewrite ?(bits.mod_to_Z (N.r247_nr_5F247 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6157 (s : N.State) (i : N.Inputs) :
  R.v6157 (state s) (inputs i) = Zmod.unsigned (N.v6157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6157 s i)) at 1.
  unfold R.v6157, N.v6157.
  rewrite ?node_6156.
  rewrite !state_r248_nr_5F248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r248_nr_5F248 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6158 (s : N.State) (i : N.Inputs) :
  R.v6158 (state s) (inputs i) = Zmod.unsigned (N.v6158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6158 s i)) at 1.
  unfold R.v6158, N.v6158.
  rewrite ?node_6157.
  rewrite !state_r249_nr_5F249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r249_nr_5F249 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6159 (s : N.State) (i : N.Inputs) :
  R.v6159 (state s) (inputs i) = Zmod.unsigned (N.v6159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6159 s i)) at 1.
  unfold R.v6159, N.v6159.
  rewrite !state_r231_nr_5F231.
  rewrite !state_r232_nr_5F232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r231_nr_5F231 s)).
  rewrite ?(bits.mod_to_Z (N.r232_nr_5F232 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6160 (s : N.State) (i : N.Inputs) :
  R.v6160 (state s) (inputs i) = Zmod.unsigned (N.v6160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6160 s i)) at 1.
  unfold R.v6160, N.v6160.
  rewrite ?node_6085.
  rewrite !state_r233_nr_5F233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r233_nr_5F233 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6161 (s : N.State) (i : N.Inputs) :
  R.v6161 (state s) (inputs i) = Zmod.unsigned (N.v6161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6161 s i)) at 1.
  unfold R.v6161, N.v6161.
  rewrite ?node_6159.
  rewrite ?node_6160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6162 (s : N.State) (i : N.Inputs) :
  R.v6162 (state s) (inputs i) = Zmod.unsigned (N.v6162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6162 s i)) at 1.
  unfold R.v6162, N.v6162.
  rewrite ?node_6158.
  rewrite ?node_6161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6163 (s : N.State) (i : N.Inputs) :
  R.v6163 (state s) (inputs i) = Zmod.unsigned (N.v6163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6163 s i)) at 1.
  unfold R.v6163, N.v6163.
  rewrite ?node_6155.
  rewrite ?node_6162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6164 (s : N.State) (i : N.Inputs) :
  R.v6164 (state s) (inputs i) = Zmod.unsigned (N.v6164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6164 s i)) at 1.
  unfold R.v6164, N.v6164.
  rewrite !state_r250_nr_5F250.
  rewrite !state_r251_nr_5F251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r250_nr_5F250 s)).
  rewrite ?(bits.mod_to_Z (N.r251_nr_5F251 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6165 (s : N.State) (i : N.Inputs) :
  R.v6165 (state s) (inputs i) = Zmod.unsigned (N.v6165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6165 s i)) at 1.
  unfold R.v6165, N.v6165.
  rewrite ?node_6164.
  rewrite !state_r252_nr_5F252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r252_nr_5F252 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6166 (s : N.State) (i : N.Inputs) :
  R.v6166 (state s) (inputs i) = Zmod.unsigned (N.v6166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6166 s i)) at 1.
  unfold R.v6166, N.v6166.
  rewrite ?node_6165.
  rewrite !state_r253_nr_5F253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r253_nr_5F253 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6167 (s : N.State) (i : N.Inputs) :
  R.v6167 (state s) (inputs i) = Zmod.unsigned (N.v6167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6167 s i)) at 1.
  unfold R.v6167, N.v6167.
  rewrite ?node_6163.
  rewrite ?node_6166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6168 (s : N.State) (i : N.Inputs) :
  R.v6168 (state s) (inputs i) = Zmod.unsigned (N.v6168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6168 s i)) at 1.
  unfold R.v6168, N.v6168.
  rewrite ?node_6076.
  rewrite ?node_6083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6169 (s : N.State) (i : N.Inputs) :
  R.v6169 (state s) (inputs i) = Zmod.unsigned (N.v6169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6169 s i)) at 1.
  unfold R.v6169, N.v6169.
  rewrite ?node_6084.
  rewrite ?node_6091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6170 (s : N.State) (i : N.Inputs) :
  R.v6170 (state s) (inputs i) = Zmod.unsigned (N.v6170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6170 s i)) at 1.
  unfold R.v6170, N.v6170.
  rewrite ?node_6168.
  rewrite ?node_6169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6171 (s : N.State) (i : N.Inputs) :
  R.v6171 (state s) (inputs i) = Zmod.unsigned (N.v6171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6171 s i)) at 1.
  unfold R.v6171, N.v6171.
  rewrite ?node_6167.
  rewrite ?node_6170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6172 (s : N.State) (i : N.Inputs) :
  R.v6172 (state s) (inputs i) = Zmod.unsigned (N.v6172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6172 s i)) at 1.
  unfold R.v6172, N.v6172.
  rewrite ?node_6071.
  rewrite !state_r226_nr_5F226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r226_nr_5F226 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6173 (s : N.State) (i : N.Inputs) :
  R.v6173 (state s) (inputs i) = Zmod.unsigned (N.v6173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6173 s i)) at 1.
  unfold R.v6173, N.v6173.
  rewrite ?node_6072.
  rewrite ?node_6075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6174 (s : N.State) (i : N.Inputs) :
  R.v6174 (state s) (inputs i) = Zmod.unsigned (N.v6174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6174 s i)) at 1.
  unfold R.v6174, N.v6174.
  rewrite ?node_6172.
  rewrite ?node_6173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6175 (s : N.State) (i : N.Inputs) :
  R.v6175 (state s) (inputs i) = Zmod.unsigned (N.v6175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6175 s i)) at 1.
  unfold R.v6175, N.v6175.
  rewrite ?node_6078.
  rewrite !state_r230_nr_5F230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r230_nr_5F230 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6176 (s : N.State) (i : N.Inputs) :
  R.v6176 (state s) (inputs i) = Zmod.unsigned (N.v6176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6176 s i)) at 1.
  unfold R.v6176, N.v6176.
  rewrite ?node_6079.
  rewrite ?node_6082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6177 (s : N.State) (i : N.Inputs) :
  R.v6177 (state s) (inputs i) = Zmod.unsigned (N.v6177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6177 s i)) at 1.
  unfold R.v6177, N.v6177.
  rewrite ?node_6175.
  rewrite ?node_6176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6178 (s : N.State) (i : N.Inputs) :
  R.v6178 (state s) (inputs i) = Zmod.unsigned (N.v6178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6178 s i)) at 1.
  unfold R.v6178, N.v6178.
  rewrite ?node_6174.
  rewrite ?node_6177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6179 (s : N.State) (i : N.Inputs) :
  R.v6179 (state s) (inputs i) = Zmod.unsigned (N.v6179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6179 s i)) at 1.
  unfold R.v6179, N.v6179.
  rewrite ?node_6086.
  rewrite !state_r234_nr_5F234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r234_nr_5F234 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6180 (s : N.State) (i : N.Inputs) :
  R.v6180 (state s) (inputs i) = Zmod.unsigned (N.v6180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6180 s i)) at 1.
  unfold R.v6180, N.v6180.
  rewrite ?node_6087.
  rewrite ?node_6090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6181 (s : N.State) (i : N.Inputs) :
  R.v6181 (state s) (inputs i) = Zmod.unsigned (N.v6181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6181 s i)) at 1.
  unfold R.v6181, N.v6181.
  rewrite ?node_6179.
  rewrite ?node_6180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6182 (s : N.State) (i : N.Inputs) :
  R.v6182 (state s) (inputs i) = Zmod.unsigned (N.v6182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6182 s i)) at 1.
  unfold R.v6182, N.v6182.
  rewrite ?node_6178.
  rewrite ?node_6181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6183 (s : N.State) (i : N.Inputs) :
  R.v6183 (state s) (inputs i) = Zmod.unsigned (N.v6183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6183 s i)) at 1.
  unfold R.v6183, N.v6183.
  rewrite !state_r235_nr_5F235.
  rewrite !state_r236_nr_5F236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r235_nr_5F235 s)).
  rewrite ?(bits.mod_to_Z (N.r236_nr_5F236 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6184 (s : N.State) (i : N.Inputs) :
  R.v6184 (state s) (inputs i) = Zmod.unsigned (N.v6184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6184 s i)) at 1.
  unfold R.v6184, N.v6184.
  rewrite ?node_6093.
  rewrite !state_r237_nr_5F237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r237_nr_5F237 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6185 (s : N.State) (i : N.Inputs) :
  R.v6185 (state s) (inputs i) = Zmod.unsigned (N.v6185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6185 s i)) at 1.
  unfold R.v6185, N.v6185.
  rewrite ?node_6183.
  rewrite ?node_6184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6186 (s : N.State) (i : N.Inputs) :
  R.v6186 (state s) (inputs i) = Zmod.unsigned (N.v6186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6186 s i)) at 1.
  unfold R.v6186, N.v6186.
  rewrite ?node_6182.
  rewrite ?node_6185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6187 (s : N.State) (i : N.Inputs) :
  R.v6187 (state s) (inputs i) = Zmod.unsigned (N.v6187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6187 s i)) at 1.
  unfold R.v6187, N.v6187.
  rewrite ?node_6102.
  rewrite ?node_6105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6188 (s : N.State) (i : N.Inputs) :
  R.v6188 (state s) (inputs i) = Zmod.unsigned (N.v6188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6188 s i)) at 1.
  unfold R.v6188, N.v6188.
  rewrite ?node_6106.
  rewrite ?node_6109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6189 (s : N.State) (i : N.Inputs) :
  R.v6189 (state s) (inputs i) = Zmod.unsigned (N.v6189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6189 s i)) at 1.
  unfold R.v6189, N.v6189.
  rewrite ?node_6187.
  rewrite ?node_6188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6190 (s : N.State) (i : N.Inputs) :
  R.v6190 (state s) (inputs i) = Zmod.unsigned (N.v6190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6190 s i)) at 1.
  unfold R.v6190, N.v6190.
  rewrite ?node_6186.
  rewrite ?node_6189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6191 (s : N.State) (i : N.Inputs) :
  R.v6191 (state s) (inputs i) = Zmod.unsigned (N.v6191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6191 s i)) at 1.
  unfold R.v6191, N.v6191.
  rewrite ?node_6171.
  rewrite ?node_6190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6192 (s : N.State) (i : N.Inputs) :
  R.v6192 (state s) (inputs i) = Zmod.unsigned (N.v6192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6192 s i)) at 1.
  unfold R.v6192, N.v6192.
  rewrite ?node_6092.
  rewrite ?node_6094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6193 (s : N.State) (i : N.Inputs) :
  R.v6193 (state s) (inputs i) = Zmod.unsigned (N.v6193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6193 s i)) at 1.
  unfold R.v6193, N.v6193.
  rewrite ?node_6095.
  rewrite ?node_6098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6194 (s : N.State) (i : N.Inputs) :
  R.v6194 (state s) (inputs i) = Zmod.unsigned (N.v6194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6194 s i)) at 1.
  unfold R.v6194, N.v6194.
  rewrite ?node_6192.
  rewrite ?node_6193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6195 (s : N.State) (i : N.Inputs) :
  R.v6195 (state s) (inputs i) = Zmod.unsigned (N.v6195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6195 s i)) at 1.
  unfold R.v6195, N.v6195.
  rewrite ?node_6191.
  rewrite ?node_6194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6196 (s : N.State) (i : N.Inputs) :
  R.v6196 (state s) (inputs i) = Zmod.unsigned (N.v6196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6196 s i)) at 1.
  unfold R.v6196, N.v6196.
  rewrite ?node_6110.
  rewrite ?node_6113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6197 (s : N.State) (i : N.Inputs) :
  R.v6197 (state s) (inputs i) = Zmod.unsigned (N.v6197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6197 s i)) at 1.
  unfold R.v6197, N.v6197.
  rewrite ?node_6114.
  rewrite ?node_6117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6198 (s : N.State) (i : N.Inputs) :
  R.v6198 (state s) (inputs i) = Zmod.unsigned (N.v6198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6198 s i)) at 1.
  unfold R.v6198, N.v6198.
  rewrite ?node_6196.
  rewrite ?node_6197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6199 (s : N.State) (i : N.Inputs) :
  R.v6199 (state s) (inputs i) = Zmod.unsigned (N.v6199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6199 s i)) at 1.
  unfold R.v6199, N.v6199.
  rewrite ?node_6195.
  rewrite ?node_6198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6200 (s : N.State) (i : N.Inputs) :
  R.v6200 (state s) (inputs i) = Zmod.unsigned (N.v6200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6200 s i)) at 1.
  unfold R.v6200, N.v6200.
  rewrite ?node_6099.
  rewrite ?node_6118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6201 (s : N.State) (i : N.Inputs) :
  R.v6201 (state s) (inputs i) = Zmod.unsigned (N.v6201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6201 s i)) at 1.
  unfold R.v6201, N.v6201.
  rewrite ?node_6119.
  rewrite ?node_6122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6202 (s : N.State) (i : N.Inputs) :
  R.v6202 (state s) (inputs i) = Zmod.unsigned (N.v6202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6202 s i)) at 1.
  unfold R.v6202, N.v6202.
  rewrite ?node_6200.
  rewrite ?node_6201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6203 (s : N.State) (i : N.Inputs) :
  R.v6203 (state s) (inputs i) = Zmod.unsigned (N.v6203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6203 s i)) at 1.
  unfold R.v6203, N.v6203.
  rewrite ?node_6199.
  rewrite ?node_6202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6204 (s : N.State) (i : N.Inputs) :
  R.v6204 (state s) (inputs i) = Zmod.unsigned (N.v6204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6204 s i)) at 1.
  unfold R.v6204, N.v6204.
  rewrite ?node_6123.
  rewrite ?node_6126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6205 (s : N.State) (i : N.Inputs) :
  R.v6205 (state s) (inputs i) = Zmod.unsigned (N.v6205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6205 s i)) at 1.
  unfold R.v6205, N.v6205.
  rewrite ?node_6127.
  rewrite ?node_6130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6206 (s : N.State) (i : N.Inputs) :
  R.v6206 (state s) (inputs i) = Zmod.unsigned (N.v6206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6206 s i)) at 1.
  unfold R.v6206, N.v6206.
  rewrite ?node_6204.
  rewrite ?node_6205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6207 (s : N.State) (i : N.Inputs) :
  R.v6207 (state s) (inputs i) = Zmod.unsigned (N.v6207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6207 s i)) at 1.
  unfold R.v6207, N.v6207.
  rewrite ?node_6203.
  rewrite ?node_6206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6208 (s : N.State) (i : N.Inputs) :
  R.v6208 (state s) (inputs i) = Zmod.unsigned (N.v6208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6208 s i)) at 1.
  unfold R.v6208, N.v6208.
  rewrite ?node_6131.
  rewrite ?node_6134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6209 (s : N.State) (i : N.Inputs) :
  R.v6209 (state s) (inputs i) = Zmod.unsigned (N.v6209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6209 s i)) at 1.
  unfold R.v6209, N.v6209.
  rewrite ?node_6207.
  rewrite ?node_6208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6210 (s : N.State) (i : N.Inputs) :
  R.v6210 (state s) (inputs i) = Zmod.unsigned (N.v6210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6210 s i)) at 1.
  unfold R.v6210, N.v6210.
  rewrite ?node_6209.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2329_nr_5F2360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2329_nr_5F2360 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6211 (s : N.State) (i : N.Inputs) :
  R.v6211 (state s) (inputs i) = Zmod.unsigned (N.v6211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6211 s i)) at 1.
  unfold R.v6211, N.v6211.
  rewrite ?node_6135.
  rewrite ?node_6136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6212 (s : N.State) (i : N.Inputs) :
  R.v6212 (state s) (inputs i) = Zmod.unsigned (N.v6212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6212 s i)) at 1.
  unfold R.v6212, N.v6212.
  rewrite ?node_6211.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2330_nr_5F2361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2330_nr_5F2361 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6213 (s : N.State) (i : N.Inputs) :
  R.v6213 (state s) (inputs i) = Zmod.unsigned (N.v6213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6213 s i)) at 1.
  unfold R.v6213, N.v6213.
  rewrite !state_r254_nr_5F254.
  rewrite !state_r255_nr_5F255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r254_nr_5F254 s)).
  rewrite ?(bits.mod_to_Z (N.r255_nr_5F255 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6214 (s : N.State) (i : N.Inputs) :
  R.v6214 (state s) (inputs i) = Zmod.unsigned (N.v6214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6214 s i)) at 1.
  unfold R.v6214, N.v6214.
  rewrite ?node_6213.
  rewrite !state_r256_nr_5F256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r256_nr_5F256 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6215 (s : N.State) (i : N.Inputs) :
  R.v6215 (state s) (inputs i) = Zmod.unsigned (N.v6215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6215 s i)) at 1.
  unfold R.v6215, N.v6215.
  rewrite ?node_6214.
  rewrite !state_r257_nr_5F257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r257_nr_5F257 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6216 (s : N.State) (i : N.Inputs) :
  R.v6216 (state s) (inputs i) = Zmod.unsigned (N.v6216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6216 s i)) at 1.
  unfold R.v6216, N.v6216.
  rewrite !state_r238_nr_5F238.
  rewrite !state_r239_nr_5F239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r238_nr_5F238 s)).
  rewrite ?(bits.mod_to_Z (N.r239_nr_5F239 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6217 (s : N.State) (i : N.Inputs) :
  R.v6217 (state s) (inputs i) = Zmod.unsigned (N.v6217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6217 s i)) at 1.
  unfold R.v6217, N.v6217.
  rewrite ?node_6141.
  rewrite !state_r240_nr_5F240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r240_nr_5F240 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6218 (s : N.State) (i : N.Inputs) :
  R.v6218 (state s) (inputs i) = Zmod.unsigned (N.v6218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6218 s i)) at 1.
  unfold R.v6218, N.v6218.
  rewrite ?node_6216.
  rewrite ?node_6217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6219 (s : N.State) (i : N.Inputs) :
  R.v6219 (state s) (inputs i) = Zmod.unsigned (N.v6219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6219 s i)) at 1.
  unfold R.v6219, N.v6219.
  rewrite ?node_6215.
  rewrite ?node_6218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6220 (s : N.State) (i : N.Inputs) :
  R.v6220 (state s) (inputs i) = Zmod.unsigned (N.v6220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6220 s i)) at 1.
  unfold R.v6220, N.v6220.
  rewrite !state_r258_nr_5F258.
  rewrite !state_r259_nr_5F259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r258_nr_5F258 s)).
  rewrite ?(bits.mod_to_Z (N.r259_nr_5F259 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6221 (s : N.State) (i : N.Inputs) :
  R.v6221 (state s) (inputs i) = Zmod.unsigned (N.v6221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6221 s i)) at 1.
  unfold R.v6221, N.v6221.
  rewrite ?node_6220.
  rewrite !state_r260_nr_5F260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r260_nr_5F260 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6222 (s : N.State) (i : N.Inputs) :
  R.v6222 (state s) (inputs i) = Zmod.unsigned (N.v6222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6222 s i)) at 1.
  unfold R.v6222, N.v6222.
  rewrite ?node_6221.
  rewrite !state_r261_nr_5F261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r261_nr_5F261 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6223 (s : N.State) (i : N.Inputs) :
  R.v6223 (state s) (inputs i) = Zmod.unsigned (N.v6223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6223 s i)) at 1.
  unfold R.v6223, N.v6223.
  rewrite !state_r242_nr_5F242.
  rewrite !state_r243_nr_5F243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r242_nr_5F242 s)).
  rewrite ?(bits.mod_to_Z (N.r243_nr_5F243 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6224 (s : N.State) (i : N.Inputs) :
  R.v6224 (state s) (inputs i) = Zmod.unsigned (N.v6224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6224 s i)) at 1.
  unfold R.v6224, N.v6224.
  rewrite ?node_6148.
  rewrite !state_r244_nr_5F244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r244_nr_5F244 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6225 (s : N.State) (i : N.Inputs) :
  R.v6225 (state s) (inputs i) = Zmod.unsigned (N.v6225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6225 s i)) at 1.
  unfold R.v6225, N.v6225.
  rewrite ?node_6223.
  rewrite ?node_6224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6226 (s : N.State) (i : N.Inputs) :
  R.v6226 (state s) (inputs i) = Zmod.unsigned (N.v6226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6226 s i)) at 1.
  unfold R.v6226, N.v6226.
  rewrite ?node_6222.
  rewrite ?node_6225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6227 (s : N.State) (i : N.Inputs) :
  R.v6227 (state s) (inputs i) = Zmod.unsigned (N.v6227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6227 s i)) at 1.
  unfold R.v6227, N.v6227.
  rewrite ?node_6219.
  rewrite ?node_6226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6228 (s : N.State) (i : N.Inputs) :
  R.v6228 (state s) (inputs i) = Zmod.unsigned (N.v6228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6228 s i)) at 1.
  unfold R.v6228, N.v6228.
  rewrite !state_r262_nr_5F262.
  rewrite !state_r263_nr_5F263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r262_nr_5F262 s)).
  rewrite ?(bits.mod_to_Z (N.r263_nr_5F263 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6229 (s : N.State) (i : N.Inputs) :
  R.v6229 (state s) (inputs i) = Zmod.unsigned (N.v6229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6229 s i)) at 1.
  unfold R.v6229, N.v6229.
  rewrite ?node_6228.
  rewrite !state_r264_nr_5F264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r264_nr_5F264 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6230 (s : N.State) (i : N.Inputs) :
  R.v6230 (state s) (inputs i) = Zmod.unsigned (N.v6230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6230 s i)) at 1.
  unfold R.v6230, N.v6230.
  rewrite ?node_6229.
  rewrite !state_r265_nr_5F265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r265_nr_5F265 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6231 (s : N.State) (i : N.Inputs) :
  R.v6231 (state s) (inputs i) = Zmod.unsigned (N.v6231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6231 s i)) at 1.
  unfold R.v6231, N.v6231.
  rewrite !state_r246_nr_5F246.
  rewrite !state_r247_nr_5F247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r246_nr_5F246 s)).
  rewrite ?(bits.mod_to_Z (N.r247_nr_5F247 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6232 (s : N.State) (i : N.Inputs) :
  R.v6232 (state s) (inputs i) = Zmod.unsigned (N.v6232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6232 s i)) at 1.
  unfold R.v6232, N.v6232.
  rewrite ?node_6156.
  rewrite !state_r248_nr_5F248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r248_nr_5F248 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6233 (s : N.State) (i : N.Inputs) :
  R.v6233 (state s) (inputs i) = Zmod.unsigned (N.v6233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6233 s i)) at 1.
  unfold R.v6233, N.v6233.
  rewrite ?node_6231.
  rewrite ?node_6232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6234 (s : N.State) (i : N.Inputs) :
  R.v6234 (state s) (inputs i) = Zmod.unsigned (N.v6234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6234 s i)) at 1.
  unfold R.v6234, N.v6234.
  rewrite ?node_6230.
  rewrite ?node_6233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6235 (s : N.State) (i : N.Inputs) :
  R.v6235 (state s) (inputs i) = Zmod.unsigned (N.v6235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6235 s i)) at 1.
  unfold R.v6235, N.v6235.
  rewrite ?node_6227.
  rewrite ?node_6234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6236 (s : N.State) (i : N.Inputs) :
  R.v6236 (state s) (inputs i) = Zmod.unsigned (N.v6236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6236 s i)) at 1.
  unfold R.v6236, N.v6236.
  rewrite !state_r266_nr_5F266.
  rewrite !state_r267_nr_5F267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r266_nr_5F266 s)).
  rewrite ?(bits.mod_to_Z (N.r267_nr_5F267 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6237 (s : N.State) (i : N.Inputs) :
  R.v6237 (state s) (inputs i) = Zmod.unsigned (N.v6237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6237 s i)) at 1.
  unfold R.v6237, N.v6237.
  rewrite ?node_6236.
  rewrite !state_r268_nr_5F268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r268_nr_5F268 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6238 (s : N.State) (i : N.Inputs) :
  R.v6238 (state s) (inputs i) = Zmod.unsigned (N.v6238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6238 s i)) at 1.
  unfold R.v6238, N.v6238.
  rewrite ?node_6237.
  rewrite !state_r269_nr_5F269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r269_nr_5F269 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6239 (s : N.State) (i : N.Inputs) :
  R.v6239 (state s) (inputs i) = Zmod.unsigned (N.v6239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6239 s i)) at 1.
  unfold R.v6239, N.v6239.
  rewrite !state_r250_nr_5F250.
  rewrite !state_r251_nr_5F251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r250_nr_5F250 s)).
  rewrite ?(bits.mod_to_Z (N.r251_nr_5F251 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6240 (s : N.State) (i : N.Inputs) :
  R.v6240 (state s) (inputs i) = Zmod.unsigned (N.v6240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6240 s i)) at 1.
  unfold R.v6240, N.v6240.
  rewrite ?node_6164.
  rewrite !state_r252_nr_5F252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r252_nr_5F252 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6241 (s : N.State) (i : N.Inputs) :
  R.v6241 (state s) (inputs i) = Zmod.unsigned (N.v6241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6241 s i)) at 1.
  unfold R.v6241, N.v6241.
  rewrite ?node_6239.
  rewrite ?node_6240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6242 (s : N.State) (i : N.Inputs) :
  R.v6242 (state s) (inputs i) = Zmod.unsigned (N.v6242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6242 s i)) at 1.
  unfold R.v6242, N.v6242.
  rewrite ?node_6238.
  rewrite ?node_6241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6243 (s : N.State) (i : N.Inputs) :
  R.v6243 (state s) (inputs i) = Zmod.unsigned (N.v6243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6243 s i)) at 1.
  unfold R.v6243, N.v6243.
  rewrite ?node_6235.
  rewrite ?node_6242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6244 (s : N.State) (i : N.Inputs) :
  R.v6244 (state s) (inputs i) = Zmod.unsigned (N.v6244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6244 s i)) at 1.
  unfold R.v6244, N.v6244.
  rewrite ?node_6147.
  rewrite ?node_6154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6245 (s : N.State) (i : N.Inputs) :
  R.v6245 (state s) (inputs i) = Zmod.unsigned (N.v6245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6245 s i)) at 1.
  unfold R.v6245, N.v6245.
  rewrite ?node_6155.
  rewrite ?node_6162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6246 (s : N.State) (i : N.Inputs) :
  R.v6246 (state s) (inputs i) = Zmod.unsigned (N.v6246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6246 s i)) at 1.
  unfold R.v6246, N.v6246.
  rewrite ?node_6244.
  rewrite ?node_6245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6247 (s : N.State) (i : N.Inputs) :
  R.v6247 (state s) (inputs i) = Zmod.unsigned (N.v6247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6247 s i)) at 1.
  unfold R.v6247, N.v6247.
  rewrite ?node_6243.
  rewrite ?node_6246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6248 (s : N.State) (i : N.Inputs) :
  R.v6248 (state s) (inputs i) = Zmod.unsigned (N.v6248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6248 s i)) at 1.
  unfold R.v6248, N.v6248.
  rewrite ?node_6142.
  rewrite !state_r241_nr_5F241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r241_nr_5F241 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6249 (s : N.State) (i : N.Inputs) :
  R.v6249 (state s) (inputs i) = Zmod.unsigned (N.v6249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6249 s i)) at 1.
  unfold R.v6249, N.v6249.
  rewrite ?node_6143.
  rewrite ?node_6146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6250 (s : N.State) (i : N.Inputs) :
  R.v6250 (state s) (inputs i) = Zmod.unsigned (N.v6250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6250 s i)) at 1.
  unfold R.v6250, N.v6250.
  rewrite ?node_6248.
  rewrite ?node_6249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6251 (s : N.State) (i : N.Inputs) :
  R.v6251 (state s) (inputs i) = Zmod.unsigned (N.v6251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6251 s i)) at 1.
  unfold R.v6251, N.v6251.
  rewrite ?node_6149.
  rewrite !state_r245_nr_5F245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r245_nr_5F245 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6252 (s : N.State) (i : N.Inputs) :
  R.v6252 (state s) (inputs i) = Zmod.unsigned (N.v6252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6252 s i)) at 1.
  unfold R.v6252, N.v6252.
  rewrite ?node_6150.
  rewrite ?node_6153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6253 (s : N.State) (i : N.Inputs) :
  R.v6253 (state s) (inputs i) = Zmod.unsigned (N.v6253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6253 s i)) at 1.
  unfold R.v6253, N.v6253.
  rewrite ?node_6251.
  rewrite ?node_6252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6254 (s : N.State) (i : N.Inputs) :
  R.v6254 (state s) (inputs i) = Zmod.unsigned (N.v6254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6254 s i)) at 1.
  unfold R.v6254, N.v6254.
  rewrite ?node_6250.
  rewrite ?node_6253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6255 (s : N.State) (i : N.Inputs) :
  R.v6255 (state s) (inputs i) = Zmod.unsigned (N.v6255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6255 s i)) at 1.
  unfold R.v6255, N.v6255.
  rewrite ?node_6157.
  rewrite !state_r249_nr_5F249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r249_nr_5F249 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6256 (s : N.State) (i : N.Inputs) :
  R.v6256 (state s) (inputs i) = Zmod.unsigned (N.v6256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6256 s i)) at 1.
  unfold R.v6256, N.v6256.
  rewrite ?node_6158.
  rewrite ?node_6161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6257 (s : N.State) (i : N.Inputs) :
  R.v6257 (state s) (inputs i) = Zmod.unsigned (N.v6257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6257 s i)) at 1.
  unfold R.v6257, N.v6257.
  rewrite ?node_6255.
  rewrite ?node_6256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6258 (s : N.State) (i : N.Inputs) :
  R.v6258 (state s) (inputs i) = Zmod.unsigned (N.v6258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6258 s i)) at 1.
  unfold R.v6258, N.v6258.
  rewrite ?node_6254.
  rewrite ?node_6257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6259 (s : N.State) (i : N.Inputs) :
  R.v6259 (state s) (inputs i) = Zmod.unsigned (N.v6259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6259 s i)) at 1.
  unfold R.v6259, N.v6259.
  rewrite ?node_6165.
  rewrite !state_r253_nr_5F253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r253_nr_5F253 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6260 (s : N.State) (i : N.Inputs) :
  R.v6260 (state s) (inputs i) = Zmod.unsigned (N.v6260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6260 s i)) at 1.
  unfold R.v6260, N.v6260.
  rewrite ?node_6258.
  rewrite ?node_6259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6261 (s : N.State) (i : N.Inputs) :
  R.v6261 (state s) (inputs i) = Zmod.unsigned (N.v6261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6261 s i)) at 1.
  unfold R.v6261, N.v6261.
  rewrite ?node_6174.
  rewrite ?node_6177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6262 (s : N.State) (i : N.Inputs) :
  R.v6262 (state s) (inputs i) = Zmod.unsigned (N.v6262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6262 s i)) at 1.
  unfold R.v6262, N.v6262.
  rewrite ?node_6178.
  rewrite ?node_6181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6263 (s : N.State) (i : N.Inputs) :
  R.v6263 (state s) (inputs i) = Zmod.unsigned (N.v6263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6263 s i)) at 1.
  unfold R.v6263, N.v6263.
  rewrite ?node_6261.
  rewrite ?node_6262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6264 (s : N.State) (i : N.Inputs) :
  R.v6264 (state s) (inputs i) = Zmod.unsigned (N.v6264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6264 s i)) at 1.
  unfold R.v6264, N.v6264.
  rewrite ?node_6260.
  rewrite ?node_6263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6265 (s : N.State) (i : N.Inputs) :
  R.v6265 (state s) (inputs i) = Zmod.unsigned (N.v6265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6265 s i)) at 1.
  unfold R.v6265, N.v6265.
  rewrite ?node_6247.
  rewrite ?node_6264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6266 (s : N.State) (i : N.Inputs) :
  R.v6266 (state s) (inputs i) = Zmod.unsigned (N.v6266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6266 s i)) at 1.
  unfold R.v6266, N.v6266.
  rewrite ?node_6163.
  rewrite ?node_6166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6267 (s : N.State) (i : N.Inputs) :
  R.v6267 (state s) (inputs i) = Zmod.unsigned (N.v6267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6267 s i)) at 1.
  unfold R.v6267, N.v6267.
  rewrite ?node_6167.
  rewrite ?node_6170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6268 (s : N.State) (i : N.Inputs) :
  R.v6268 (state s) (inputs i) = Zmod.unsigned (N.v6268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6268 s i)) at 1.
  unfold R.v6268, N.v6268.
  rewrite ?node_6266.
  rewrite ?node_6267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6269 (s : N.State) (i : N.Inputs) :
  R.v6269 (state s) (inputs i) = Zmod.unsigned (N.v6269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6269 s i)) at 1.
  unfold R.v6269, N.v6269.
  rewrite ?node_6265.
  rewrite ?node_6268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6270 (s : N.State) (i : N.Inputs) :
  R.v6270 (state s) (inputs i) = Zmod.unsigned (N.v6270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6270 s i)) at 1.
  unfold R.v6270, N.v6270.
  rewrite ?node_6182.
  rewrite ?node_6185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6271 (s : N.State) (i : N.Inputs) :
  R.v6271 (state s) (inputs i) = Zmod.unsigned (N.v6271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6271 s i)) at 1.
  unfold R.v6271, N.v6271.
  rewrite ?node_6186.
  rewrite ?node_6189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6272 (s : N.State) (i : N.Inputs) :
  R.v6272 (state s) (inputs i) = Zmod.unsigned (N.v6272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6272 s i)) at 1.
  unfold R.v6272, N.v6272.
  rewrite ?node_6270.
  rewrite ?node_6271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6273 (s : N.State) (i : N.Inputs) :
  R.v6273 (state s) (inputs i) = Zmod.unsigned (N.v6273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6273 s i)) at 1.
  unfold R.v6273, N.v6273.
  rewrite ?node_6269.
  rewrite ?node_6272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6274 (s : N.State) (i : N.Inputs) :
  R.v6274 (state s) (inputs i) = Zmod.unsigned (N.v6274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6274 s i)) at 1.
  unfold R.v6274, N.v6274.
  rewrite ?node_6171.
  rewrite ?node_6190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6275 (s : N.State) (i : N.Inputs) :
  R.v6275 (state s) (inputs i) = Zmod.unsigned (N.v6275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6275 s i)) at 1.
  unfold R.v6275, N.v6275.
  rewrite ?node_6191.
  rewrite ?node_6194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6276 (s : N.State) (i : N.Inputs) :
  R.v6276 (state s) (inputs i) = Zmod.unsigned (N.v6276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6276 s i)) at 1.
  unfold R.v6276, N.v6276.
  rewrite ?node_6274.
  rewrite ?node_6275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6277 (s : N.State) (i : N.Inputs) :
  R.v6277 (state s) (inputs i) = Zmod.unsigned (N.v6277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6277 s i)) at 1.
  unfold R.v6277, N.v6277.
  rewrite ?node_6273.
  rewrite ?node_6276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6278 (s : N.State) (i : N.Inputs) :
  R.v6278 (state s) (inputs i) = Zmod.unsigned (N.v6278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6278 s i)) at 1.
  unfold R.v6278, N.v6278.
  rewrite ?node_6195.
  rewrite ?node_6198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6279 (s : N.State) (i : N.Inputs) :
  R.v6279 (state s) (inputs i) = Zmod.unsigned (N.v6279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6279 s i)) at 1.
  unfold R.v6279, N.v6279.
  rewrite ?node_6199.
  rewrite ?node_6202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6280 (s : N.State) (i : N.Inputs) :
  R.v6280 (state s) (inputs i) = Zmod.unsigned (N.v6280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6280 s i)) at 1.
  unfold R.v6280, N.v6280.
  rewrite ?node_6278.
  rewrite ?node_6279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6281 (s : N.State) (i : N.Inputs) :
  R.v6281 (state s) (inputs i) = Zmod.unsigned (N.v6281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6281 s i)) at 1.
  unfold R.v6281, N.v6281.
  rewrite ?node_6277.
  rewrite ?node_6280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6282 (s : N.State) (i : N.Inputs) :
  R.v6282 (state s) (inputs i) = Zmod.unsigned (N.v6282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6282 s i)) at 1.
  unfold R.v6282, N.v6282.
  rewrite ?node_6203.
  rewrite ?node_6206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6283 (s : N.State) (i : N.Inputs) :
  R.v6283 (state s) (inputs i) = Zmod.unsigned (N.v6283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6283 s i)) at 1.
  unfold R.v6283, N.v6283.
  rewrite ?node_6281.
  rewrite ?node_6282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6284 (s : N.State) (i : N.Inputs) :
  R.v6284 (state s) (inputs i) = Zmod.unsigned (N.v6284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6284 s i)) at 1.
  unfold R.v6284, N.v6284.
  rewrite ?node_6283.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2331_nr_5F2362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2331_nr_5F2362 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6285 (s : N.State) (i : N.Inputs) :
  R.v6285 (state s) (inputs i) = Zmod.unsigned (N.v6285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6285 s i)) at 1.
  unfold R.v6285, N.v6285.
  rewrite ?node_6207.
  rewrite ?node_6208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6286 (s : N.State) (i : N.Inputs) :
  R.v6286 (state s) (inputs i) = Zmod.unsigned (N.v6286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6286 s i)) at 1.
  unfold R.v6286, N.v6286.
  rewrite ?node_6285.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2332_nr_5F2363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2332_nr_5F2363 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6287 (s : N.State) (i : N.Inputs) :
  R.v6287 (state s) (inputs i) = Zmod.unsigned (N.v6287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6287 s i)) at 1.
  unfold R.v6287, N.v6287.
  rewrite !state_r270_nr_5F270.
  rewrite !state_r271_nr_5F271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r270_nr_5F270 s)).
  rewrite ?(bits.mod_to_Z (N.r271_nr_5F271 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6288 (s : N.State) (i : N.Inputs) :
  R.v6288 (state s) (inputs i) = Zmod.unsigned (N.v6288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6288 s i)) at 1.
  unfold R.v6288, N.v6288.
  rewrite ?node_6287.
  rewrite !state_r272_nr_5F272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r272_nr_5F272 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6289 (s : N.State) (i : N.Inputs) :
  R.v6289 (state s) (inputs i) = Zmod.unsigned (N.v6289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6289 s i)) at 1.
  unfold R.v6289, N.v6289.
  rewrite ?node_6288.
  rewrite !state_r273_nr_5F273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r273_nr_5F273 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6290 (s : N.State) (i : N.Inputs) :
  R.v6290 (state s) (inputs i) = Zmod.unsigned (N.v6290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6290 s i)) at 1.
  unfold R.v6290, N.v6290.
  rewrite !state_r254_nr_5F254.
  rewrite !state_r255_nr_5F255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r254_nr_5F254 s)).
  rewrite ?(bits.mod_to_Z (N.r255_nr_5F255 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6291 (s : N.State) (i : N.Inputs) :
  R.v6291 (state s) (inputs i) = Zmod.unsigned (N.v6291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6291 s i)) at 1.
  unfold R.v6291, N.v6291.
  rewrite ?node_6213.
  rewrite !state_r256_nr_5F256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r256_nr_5F256 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6292 (s : N.State) (i : N.Inputs) :
  R.v6292 (state s) (inputs i) = Zmod.unsigned (N.v6292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6292 s i)) at 1.
  unfold R.v6292, N.v6292.
  rewrite ?node_6290.
  rewrite ?node_6291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6293 (s : N.State) (i : N.Inputs) :
  R.v6293 (state s) (inputs i) = Zmod.unsigned (N.v6293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6293 s i)) at 1.
  unfold R.v6293, N.v6293.
  rewrite ?node_6289.
  rewrite ?node_6292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6294 (s : N.State) (i : N.Inputs) :
  R.v6294 (state s) (inputs i) = Zmod.unsigned (N.v6294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6294 s i)) at 1.
  unfold R.v6294, N.v6294.
  rewrite !state_r274_nr_5F274.
  rewrite !state_r275_nr_5F275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r274_nr_5F274 s)).
  rewrite ?(bits.mod_to_Z (N.r275_nr_5F275 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6295 (s : N.State) (i : N.Inputs) :
  R.v6295 (state s) (inputs i) = Zmod.unsigned (N.v6295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6295 s i)) at 1.
  unfold R.v6295, N.v6295.
  rewrite ?node_6294.
  rewrite !state_r276_nr_5F276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r276_nr_5F276 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6296 (s : N.State) (i : N.Inputs) :
  R.v6296 (state s) (inputs i) = Zmod.unsigned (N.v6296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6296 s i)) at 1.
  unfold R.v6296, N.v6296.
  rewrite ?node_6295.
  rewrite !state_r277_nr_5F277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r277_nr_5F277 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6297 (s : N.State) (i : N.Inputs) :
  R.v6297 (state s) (inputs i) = Zmod.unsigned (N.v6297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6297 s i)) at 1.
  unfold R.v6297, N.v6297.
  rewrite !state_r258_nr_5F258.
  rewrite !state_r259_nr_5F259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r258_nr_5F258 s)).
  rewrite ?(bits.mod_to_Z (N.r259_nr_5F259 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6298 (s : N.State) (i : N.Inputs) :
  R.v6298 (state s) (inputs i) = Zmod.unsigned (N.v6298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6298 s i)) at 1.
  unfold R.v6298, N.v6298.
  rewrite ?node_6220.
  rewrite !state_r260_nr_5F260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r260_nr_5F260 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6299 (s : N.State) (i : N.Inputs) :
  R.v6299 (state s) (inputs i) = Zmod.unsigned (N.v6299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6299 s i)) at 1.
  unfold R.v6299, N.v6299.
  rewrite ?node_6297.
  rewrite ?node_6298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6300 (s : N.State) (i : N.Inputs) :
  R.v6300 (state s) (inputs i) = Zmod.unsigned (N.v6300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6300 s i)) at 1.
  unfold R.v6300, N.v6300.
  rewrite ?node_6296.
  rewrite ?node_6299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6301 (s : N.State) (i : N.Inputs) :
  R.v6301 (state s) (inputs i) = Zmod.unsigned (N.v6301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6301 s i)) at 1.
  unfold R.v6301, N.v6301.
  rewrite ?node_6293.
  rewrite ?node_6300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6302 (s : N.State) (i : N.Inputs) :
  R.v6302 (state s) (inputs i) = Zmod.unsigned (N.v6302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6302 s i)) at 1.
  unfold R.v6302, N.v6302.
  rewrite !state_r278_nr_5F278.
  rewrite !state_r279_nr_5F279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r278_nr_5F278 s)).
  rewrite ?(bits.mod_to_Z (N.r279_nr_5F279 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6303 (s : N.State) (i : N.Inputs) :
  R.v6303 (state s) (inputs i) = Zmod.unsigned (N.v6303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6303 s i)) at 1.
  unfold R.v6303, N.v6303.
  rewrite ?node_6302.
  rewrite !state_r280_nr_5F280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r280_nr_5F280 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6304 (s : N.State) (i : N.Inputs) :
  R.v6304 (state s) (inputs i) = Zmod.unsigned (N.v6304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6304 s i)) at 1.
  unfold R.v6304, N.v6304.
  rewrite ?node_6303.
  rewrite !state_r281_nr_5F281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r281_nr_5F281 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6305 (s : N.State) (i : N.Inputs) :
  R.v6305 (state s) (inputs i) = Zmod.unsigned (N.v6305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6305 s i)) at 1.
  unfold R.v6305, N.v6305.
  rewrite !state_r262_nr_5F262.
  rewrite !state_r263_nr_5F263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r262_nr_5F262 s)).
  rewrite ?(bits.mod_to_Z (N.r263_nr_5F263 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6306 (s : N.State) (i : N.Inputs) :
  R.v6306 (state s) (inputs i) = Zmod.unsigned (N.v6306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6306 s i)) at 1.
  unfold R.v6306, N.v6306.
  rewrite ?node_6228.
  rewrite !state_r264_nr_5F264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r264_nr_5F264 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6307 (s : N.State) (i : N.Inputs) :
  R.v6307 (state s) (inputs i) = Zmod.unsigned (N.v6307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6307 s i)) at 1.
  unfold R.v6307, N.v6307.
  rewrite ?node_6305.
  rewrite ?node_6306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6308 (s : N.State) (i : N.Inputs) :
  R.v6308 (state s) (inputs i) = Zmod.unsigned (N.v6308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6308 s i)) at 1.
  unfold R.v6308, N.v6308.
  rewrite ?node_6304.
  rewrite ?node_6307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6309 (s : N.State) (i : N.Inputs) :
  R.v6309 (state s) (inputs i) = Zmod.unsigned (N.v6309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6309 s i)) at 1.
  unfold R.v6309, N.v6309.
  rewrite ?node_6301.
  rewrite ?node_6308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6310 (s : N.State) (i : N.Inputs) :
  R.v6310 (state s) (inputs i) = Zmod.unsigned (N.v6310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6310 s i)) at 1.
  unfold R.v6310, N.v6310.
  rewrite !state_r282_nr_5F282.
  rewrite !state_r283_nr_5F283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r282_nr_5F282 s)).
  rewrite ?(bits.mod_to_Z (N.r283_nr_5F283 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6311 (s : N.State) (i : N.Inputs) :
  R.v6311 (state s) (inputs i) = Zmod.unsigned (N.v6311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6311 s i)) at 1.
  unfold R.v6311, N.v6311.
  rewrite ?node_6310.
  rewrite !state_r284_nr_5F284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r284_nr_5F284 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6312 (s : N.State) (i : N.Inputs) :
  R.v6312 (state s) (inputs i) = Zmod.unsigned (N.v6312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6312 s i)) at 1.
  unfold R.v6312, N.v6312.
  rewrite ?node_6311.
  rewrite !state_r285_nr_5F285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r285_nr_5F285 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6313 (s : N.State) (i : N.Inputs) :
  R.v6313 (state s) (inputs i) = Zmod.unsigned (N.v6313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6313 s i)) at 1.
  unfold R.v6313, N.v6313.
  rewrite !state_r266_nr_5F266.
  rewrite !state_r267_nr_5F267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r266_nr_5F266 s)).
  rewrite ?(bits.mod_to_Z (N.r267_nr_5F267 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6314 (s : N.State) (i : N.Inputs) :
  R.v6314 (state s) (inputs i) = Zmod.unsigned (N.v6314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6314 s i)) at 1.
  unfold R.v6314, N.v6314.
  rewrite ?node_6236.
  rewrite !state_r268_nr_5F268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r268_nr_5F268 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6315 (s : N.State) (i : N.Inputs) :
  R.v6315 (state s) (inputs i) = Zmod.unsigned (N.v6315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6315 s i)) at 1.
  unfold R.v6315, N.v6315.
  rewrite ?node_6313.
  rewrite ?node_6314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6316 (s : N.State) (i : N.Inputs) :
  R.v6316 (state s) (inputs i) = Zmod.unsigned (N.v6316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6316 s i)) at 1.
  unfold R.v6316, N.v6316.
  rewrite ?node_6312.
  rewrite ?node_6315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6317 (s : N.State) (i : N.Inputs) :
  R.v6317 (state s) (inputs i) = Zmod.unsigned (N.v6317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6317 s i)) at 1.
  unfold R.v6317, N.v6317.
  rewrite ?node_6309.
  rewrite ?node_6316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6318 (s : N.State) (i : N.Inputs) :
  R.v6318 (state s) (inputs i) = Zmod.unsigned (N.v6318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6318 s i)) at 1.
  unfold R.v6318, N.v6318.
  rewrite ?node_6219.
  rewrite ?node_6226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6319 (s : N.State) (i : N.Inputs) :
  R.v6319 (state s) (inputs i) = Zmod.unsigned (N.v6319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6319 s i)) at 1.
  unfold R.v6319, N.v6319.
  rewrite ?node_6227.
  rewrite ?node_6234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6320 (s : N.State) (i : N.Inputs) :
  R.v6320 (state s) (inputs i) = Zmod.unsigned (N.v6320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6320 s i)) at 1.
  unfold R.v6320, N.v6320.
  rewrite ?node_6318.
  rewrite ?node_6319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6321 (s : N.State) (i : N.Inputs) :
  R.v6321 (state s) (inputs i) = Zmod.unsigned (N.v6321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6321 s i)) at 1.
  unfold R.v6321, N.v6321.
  rewrite ?node_6317.
  rewrite ?node_6320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6322 (s : N.State) (i : N.Inputs) :
  R.v6322 (state s) (inputs i) = Zmod.unsigned (N.v6322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6322 s i)) at 1.
  unfold R.v6322, N.v6322.
  rewrite ?node_6214.
  rewrite !state_r257_nr_5F257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r257_nr_5F257 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6323 (s : N.State) (i : N.Inputs) :
  R.v6323 (state s) (inputs i) = Zmod.unsigned (N.v6323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6323 s i)) at 1.
  unfold R.v6323, N.v6323.
  rewrite ?node_6215.
  rewrite ?node_6218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6324 (s : N.State) (i : N.Inputs) :
  R.v6324 (state s) (inputs i) = Zmod.unsigned (N.v6324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6324 s i)) at 1.
  unfold R.v6324, N.v6324.
  rewrite ?node_6322.
  rewrite ?node_6323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6325 (s : N.State) (i : N.Inputs) :
  R.v6325 (state s) (inputs i) = Zmod.unsigned (N.v6325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6325 s i)) at 1.
  unfold R.v6325, N.v6325.
  rewrite ?node_6324.
  rewrite !state_r286_nr_5F286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r286_nr_5F286 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6326 (s : N.State) (i : N.Inputs) :
  R.v6326 (state s) (inputs i) = Zmod.unsigned (N.v6326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6326 s i)) at 1.
  unfold R.v6326, N.v6326.
  rewrite ?node_6221.
  rewrite !state_r261_nr_5F261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r261_nr_5F261 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6327 (s : N.State) (i : N.Inputs) :
  R.v6327 (state s) (inputs i) = Zmod.unsigned (N.v6327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6327 s i)) at 1.
  unfold R.v6327, N.v6327.
  rewrite ?node_6222.
  rewrite ?node_6225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6328 (s : N.State) (i : N.Inputs) :
  R.v6328 (state s) (inputs i) = Zmod.unsigned (N.v6328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6328 s i)) at 1.
  unfold R.v6328, N.v6328.
  rewrite ?node_6326.
  rewrite ?node_6327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6329 (s : N.State) (i : N.Inputs) :
  R.v6329 (state s) (inputs i) = Zmod.unsigned (N.v6329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6329 s i)) at 1.
  unfold R.v6329, N.v6329.
  rewrite ?node_6325.
  rewrite ?node_6328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6330 (s : N.State) (i : N.Inputs) :
  R.v6330 (state s) (inputs i) = Zmod.unsigned (N.v6330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6330 s i)) at 1.
  unfold R.v6330, N.v6330.
  rewrite ?node_6229.
  rewrite !state_r265_nr_5F265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r265_nr_5F265 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6331 (s : N.State) (i : N.Inputs) :
  R.v6331 (state s) (inputs i) = Zmod.unsigned (N.v6331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6331 s i)) at 1.
  unfold R.v6331, N.v6331.
  rewrite ?node_6230.
  rewrite ?node_6233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6332 (s : N.State) (i : N.Inputs) :
  R.v6332 (state s) (inputs i) = Zmod.unsigned (N.v6332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6332 s i)) at 1.
  unfold R.v6332, N.v6332.
  rewrite ?node_6330.
  rewrite ?node_6331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6333 (s : N.State) (i : N.Inputs) :
  R.v6333 (state s) (inputs i) = Zmod.unsigned (N.v6333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6333 s i)) at 1.
  unfold R.v6333, N.v6333.
  rewrite ?node_6329.
  rewrite ?node_6332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6334 (s : N.State) (i : N.Inputs) :
  R.v6334 (state s) (inputs i) = Zmod.unsigned (N.v6334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6334 s i)) at 1.
  unfold R.v6334, N.v6334.
  rewrite ?node_6250.
  rewrite ?node_6253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6335 (s : N.State) (i : N.Inputs) :
  R.v6335 (state s) (inputs i) = Zmod.unsigned (N.v6335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6335 s i)) at 1.
  unfold R.v6335, N.v6335.
  rewrite ?node_6254.
  rewrite ?node_6257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6336 (s : N.State) (i : N.Inputs) :
  R.v6336 (state s) (inputs i) = Zmod.unsigned (N.v6336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6336 s i)) at 1.
  unfold R.v6336, N.v6336.
  rewrite ?node_6334.
  rewrite ?node_6335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6337 (s : N.State) (i : N.Inputs) :
  R.v6337 (state s) (inputs i) = Zmod.unsigned (N.v6337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6337 s i)) at 1.
  unfold R.v6337, N.v6337.
  rewrite ?node_6333.
  rewrite ?node_6336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6338 (s : N.State) (i : N.Inputs) :
  R.v6338 (state s) (inputs i) = Zmod.unsigned (N.v6338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6338 s i)) at 1.
  unfold R.v6338, N.v6338.
  rewrite ?node_6321.
  rewrite ?node_6337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6339 (s : N.State) (i : N.Inputs) :
  R.v6339 (state s) (inputs i) = Zmod.unsigned (N.v6339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6339 s i)) at 1.
  unfold R.v6339, N.v6339.
  rewrite ?node_6237.
  rewrite !state_r269_nr_5F269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r269_nr_5F269 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6340 (s : N.State) (i : N.Inputs) :
  R.v6340 (state s) (inputs i) = Zmod.unsigned (N.v6340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6340 s i)) at 1.
  unfold R.v6340, N.v6340.
  rewrite ?node_6238.
  rewrite ?node_6241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6341 (s : N.State) (i : N.Inputs) :
  R.v6341 (state s) (inputs i) = Zmod.unsigned (N.v6341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6341 s i)) at 1.
  unfold R.v6341, N.v6341.
  rewrite ?node_6339.
  rewrite ?node_6340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6342 (s : N.State) (i : N.Inputs) :
  R.v6342 (state s) (inputs i) = Zmod.unsigned (N.v6342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6342 s i)) at 1.
  unfold R.v6342, N.v6342.
  rewrite ?node_6338.
  rewrite ?node_6341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6343 (s : N.State) (i : N.Inputs) :
  R.v6343 (state s) (inputs i) = Zmod.unsigned (N.v6343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6343 s i)) at 1.
  unfold R.v6343, N.v6343.
  rewrite ?node_6235.
  rewrite ?node_6242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6344 (s : N.State) (i : N.Inputs) :
  R.v6344 (state s) (inputs i) = Zmod.unsigned (N.v6344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6344 s i)) at 1.
  unfold R.v6344, N.v6344.
  rewrite ?node_6243.
  rewrite ?node_6246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6345 (s : N.State) (i : N.Inputs) :
  R.v6345 (state s) (inputs i) = Zmod.unsigned (N.v6345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6345 s i)) at 1.
  unfold R.v6345, N.v6345.
  rewrite ?node_6343.
  rewrite ?node_6344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6346 (s : N.State) (i : N.Inputs) :
  R.v6346 (state s) (inputs i) = Zmod.unsigned (N.v6346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6346 s i)) at 1.
  unfold R.v6346, N.v6346.
  rewrite ?node_6342.
  rewrite ?node_6345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6347 (s : N.State) (i : N.Inputs) :
  R.v6347 (state s) (inputs i) = Zmod.unsigned (N.v6347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6347 s i)) at 1.
  unfold R.v6347, N.v6347.
  rewrite ?node_6247.
  rewrite ?node_6264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6348 (s : N.State) (i : N.Inputs) :
  R.v6348 (state s) (inputs i) = Zmod.unsigned (N.v6348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6348 s i)) at 1.
  unfold R.v6348, N.v6348.
  rewrite ?node_6265.
  rewrite ?node_6268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6349 (s : N.State) (i : N.Inputs) :
  R.v6349 (state s) (inputs i) = Zmod.unsigned (N.v6349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6349 s i)) at 1.
  unfold R.v6349, N.v6349.
  rewrite ?node_6347.
  rewrite ?node_6348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6350 (s : N.State) (i : N.Inputs) :
  R.v6350 (state s) (inputs i) = Zmod.unsigned (N.v6350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6350 s i)) at 1.
  unfold R.v6350, N.v6350.
  rewrite ?node_6346.
  rewrite ?node_6349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6351 (s : N.State) (i : N.Inputs) :
  R.v6351 (state s) (inputs i) = Zmod.unsigned (N.v6351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6351 s i)) at 1.
  unfold R.v6351, N.v6351.
  rewrite ?node_6258.
  rewrite ?node_6259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6352 (s : N.State) (i : N.Inputs) :
  R.v6352 (state s) (inputs i) = Zmod.unsigned (N.v6352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6352 s i)) at 1.
  unfold R.v6352, N.v6352.
  rewrite ?node_6260.
  rewrite ?node_6263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6353 (s : N.State) (i : N.Inputs) :
  R.v6353 (state s) (inputs i) = Zmod.unsigned (N.v6353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6353 s i)) at 1.
  unfold R.v6353, N.v6353.
  rewrite ?node_6351.
  rewrite ?node_6352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6354 (s : N.State) (i : N.Inputs) :
  R.v6354 (state s) (inputs i) = Zmod.unsigned (N.v6354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6354 s i)) at 1.
  unfold R.v6354, N.v6354.
  rewrite ?node_6350.
  rewrite ?node_6353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6355 (s : N.State) (i : N.Inputs) :
  R.v6355 (state s) (inputs i) = Zmod.unsigned (N.v6355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6355 s i)) at 1.
  unfold R.v6355, N.v6355.
  rewrite ?node_6269.
  rewrite ?node_6272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6356 (s : N.State) (i : N.Inputs) :
  R.v6356 (state s) (inputs i) = Zmod.unsigned (N.v6356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6356 s i)) at 1.
  unfold R.v6356, N.v6356.
  rewrite ?node_6273.
  rewrite ?node_6276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6357 (s : N.State) (i : N.Inputs) :
  R.v6357 (state s) (inputs i) = Zmod.unsigned (N.v6357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6357 s i)) at 1.
  unfold R.v6357, N.v6357.
  rewrite ?node_6355.
  rewrite ?node_6356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6358 (s : N.State) (i : N.Inputs) :
  R.v6358 (state s) (inputs i) = Zmod.unsigned (N.v6358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6358 s i)) at 1.
  unfold R.v6358, N.v6358.
  rewrite ?node_6354.
  rewrite ?node_6357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6359 (s : N.State) (i : N.Inputs) :
  R.v6359 (state s) (inputs i) = Zmod.unsigned (N.v6359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6359 s i)) at 1.
  unfold R.v6359, N.v6359.
  rewrite ?node_6277.
  rewrite ?node_6280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6360 (s : N.State) (i : N.Inputs) :
  R.v6360 (state s) (inputs i) = Zmod.unsigned (N.v6360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6360 s i)) at 1.
  unfold R.v6360, N.v6360.
  rewrite ?node_6358.
  rewrite ?node_6359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6361 (s : N.State) (i : N.Inputs) :
  R.v6361 (state s) (inputs i) = Zmod.unsigned (N.v6361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6361 s i)) at 1.
  unfold R.v6361, N.v6361.
  rewrite ?node_6360.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2333_nr_5F2364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2333_nr_5F2364 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6362 (s : N.State) (i : N.Inputs) :
  R.v6362 (state s) (inputs i) = Zmod.unsigned (N.v6362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6362 s i)) at 1.
  unfold R.v6362, N.v6362.
  rewrite ?node_6281.
  rewrite ?node_6282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6363 (s : N.State) (i : N.Inputs) :
  R.v6363 (state s) (inputs i) = Zmod.unsigned (N.v6363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6363 s i)) at 1.
  unfold R.v6363, N.v6363.
  rewrite ?node_6362.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2334_nr_5F2365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2334_nr_5F2365 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6364 (s : N.State) (i : N.Inputs) :
  R.v6364 (state s) (inputs i) = Zmod.unsigned (N.v6364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6364 s i)) at 1.
  unfold R.v6364, N.v6364.
  rewrite !state_r287_nr_5F287.
  rewrite !state_r288_nr_5F288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r287_nr_5F287 s)).
  rewrite ?(bits.mod_to_Z (N.r288_nr_5F288 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6365 (s : N.State) (i : N.Inputs) :
  R.v6365 (state s) (inputs i) = Zmod.unsigned (N.v6365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6365 s i)) at 1.
  unfold R.v6365, N.v6365.
  rewrite ?node_6364.
  rewrite !state_r289_nr_5F289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r289_nr_5F289 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6366 (s : N.State) (i : N.Inputs) :
  R.v6366 (state s) (inputs i) = Zmod.unsigned (N.v6366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6366 s i)) at 1.
  unfold R.v6366, N.v6366.
  rewrite ?node_6365.
  rewrite !state_r290_nr_5F290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r290_nr_5F290 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6367 (s : N.State) (i : N.Inputs) :
  R.v6367 (state s) (inputs i) = Zmod.unsigned (N.v6367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6367 s i)) at 1.
  unfold R.v6367, N.v6367.
  rewrite !state_r270_nr_5F270.
  rewrite !state_r271_nr_5F271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r270_nr_5F270 s)).
  rewrite ?(bits.mod_to_Z (N.r271_nr_5F271 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6368 (s : N.State) (i : N.Inputs) :
  R.v6368 (state s) (inputs i) = Zmod.unsigned (N.v6368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6368 s i)) at 1.
  unfold R.v6368, N.v6368.
  rewrite ?node_6287.
  rewrite !state_r272_nr_5F272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r272_nr_5F272 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6369 (s : N.State) (i : N.Inputs) :
  R.v6369 (state s) (inputs i) = Zmod.unsigned (N.v6369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6369 s i)) at 1.
  unfold R.v6369, N.v6369.
  rewrite ?node_6367.
  rewrite ?node_6368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6370 (s : N.State) (i : N.Inputs) :
  R.v6370 (state s) (inputs i) = Zmod.unsigned (N.v6370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6370 s i)) at 1.
  unfold R.v6370, N.v6370.
  rewrite ?node_6366.
  rewrite ?node_6369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6371 (s : N.State) (i : N.Inputs) :
  R.v6371 (state s) (inputs i) = Zmod.unsigned (N.v6371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6371 s i)) at 1.
  unfold R.v6371, N.v6371.
  rewrite !state_r291_nr_5F291.
  rewrite !state_r292_nr_5F292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r291_nr_5F291 s)).
  rewrite ?(bits.mod_to_Z (N.r292_nr_5F292 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6372 (s : N.State) (i : N.Inputs) :
  R.v6372 (state s) (inputs i) = Zmod.unsigned (N.v6372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6372 s i)) at 1.
  unfold R.v6372, N.v6372.
  rewrite ?node_6371.
  rewrite !state_r293_nr_5F293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r293_nr_5F293 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6373 (s : N.State) (i : N.Inputs) :
  R.v6373 (state s) (inputs i) = Zmod.unsigned (N.v6373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6373 s i)) at 1.
  unfold R.v6373, N.v6373.
  rewrite ?node_6372.
  rewrite !state_r294_nr_5F294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r294_nr_5F294 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6374 (s : N.State) (i : N.Inputs) :
  R.v6374 (state s) (inputs i) = Zmod.unsigned (N.v6374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6374 s i)) at 1.
  unfold R.v6374, N.v6374.
  rewrite !state_r274_nr_5F274.
  rewrite !state_r275_nr_5F275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r274_nr_5F274 s)).
  rewrite ?(bits.mod_to_Z (N.r275_nr_5F275 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6375 (s : N.State) (i : N.Inputs) :
  R.v6375 (state s) (inputs i) = Zmod.unsigned (N.v6375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6375 s i)) at 1.
  unfold R.v6375, N.v6375.
  rewrite ?node_6294.
  rewrite !state_r276_nr_5F276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r276_nr_5F276 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6376 (s : N.State) (i : N.Inputs) :
  R.v6376 (state s) (inputs i) = Zmod.unsigned (N.v6376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6376 s i)) at 1.
  unfold R.v6376, N.v6376.
  rewrite ?node_6374.
  rewrite ?node_6375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6377 (s : N.State) (i : N.Inputs) :
  R.v6377 (state s) (inputs i) = Zmod.unsigned (N.v6377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6377 s i)) at 1.
  unfold R.v6377, N.v6377.
  rewrite ?node_6373.
  rewrite ?node_6376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6378 (s : N.State) (i : N.Inputs) :
  R.v6378 (state s) (inputs i) = Zmod.unsigned (N.v6378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6378 s i)) at 1.
  unfold R.v6378, N.v6378.
  rewrite ?node_6370.
  rewrite ?node_6377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6379 (s : N.State) (i : N.Inputs) :
  R.v6379 (state s) (inputs i) = Zmod.unsigned (N.v6379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6379 s i)) at 1.
  unfold R.v6379, N.v6379.
  rewrite !state_r295_nr_5F295.
  rewrite !state_r296_nr_5F296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r295_nr_5F295 s)).
  rewrite ?(bits.mod_to_Z (N.r296_nr_5F296 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6380 (s : N.State) (i : N.Inputs) :
  R.v6380 (state s) (inputs i) = Zmod.unsigned (N.v6380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6380 s i)) at 1.
  unfold R.v6380, N.v6380.
  rewrite ?node_6379.
  rewrite !state_r297_nr_5F297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r297_nr_5F297 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6381 (s : N.State) (i : N.Inputs) :
  R.v6381 (state s) (inputs i) = Zmod.unsigned (N.v6381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6381 s i)) at 1.
  unfold R.v6381, N.v6381.
  rewrite ?node_6380.
  rewrite !state_r298_nr_5F298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r298_nr_5F298 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6382 (s : N.State) (i : N.Inputs) :
  R.v6382 (state s) (inputs i) = Zmod.unsigned (N.v6382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6382 s i)) at 1.
  unfold R.v6382, N.v6382.
  rewrite !state_r278_nr_5F278.
  rewrite !state_r279_nr_5F279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r278_nr_5F278 s)).
  rewrite ?(bits.mod_to_Z (N.r279_nr_5F279 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6383 (s : N.State) (i : N.Inputs) :
  R.v6383 (state s) (inputs i) = Zmod.unsigned (N.v6383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6383 s i)) at 1.
  unfold R.v6383, N.v6383.
  rewrite ?node_6302.
  rewrite !state_r280_nr_5F280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r280_nr_5F280 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6384 (s : N.State) (i : N.Inputs) :
  R.v6384 (state s) (inputs i) = Zmod.unsigned (N.v6384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6384 s i)) at 1.
  unfold R.v6384, N.v6384.
  rewrite ?node_6382.
  rewrite ?node_6383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6385 (s : N.State) (i : N.Inputs) :
  R.v6385 (state s) (inputs i) = Zmod.unsigned (N.v6385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6385 s i)) at 1.
  unfold R.v6385, N.v6385.
  rewrite ?node_6381.
  rewrite ?node_6384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6386 (s : N.State) (i : N.Inputs) :
  R.v6386 (state s) (inputs i) = Zmod.unsigned (N.v6386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6386 s i)) at 1.
  unfold R.v6386, N.v6386.
  rewrite ?node_6378.
  rewrite ?node_6385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6387 (s : N.State) (i : N.Inputs) :
  R.v6387 (state s) (inputs i) = Zmod.unsigned (N.v6387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6387 s i)) at 1.
  unfold R.v6387, N.v6387.
  rewrite !state_r299_nr_5F299.
  rewrite !state_r300_nr_5F300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r299_nr_5F299 s)).
  rewrite ?(bits.mod_to_Z (N.r300_nr_5F300 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6388 (s : N.State) (i : N.Inputs) :
  R.v6388 (state s) (inputs i) = Zmod.unsigned (N.v6388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6388 s i)) at 1.
  unfold R.v6388, N.v6388.
  rewrite ?node_6387.
  rewrite !state_r301_nr_5F301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r301_nr_5F301 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6389 (s : N.State) (i : N.Inputs) :
  R.v6389 (state s) (inputs i) = Zmod.unsigned (N.v6389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6389 s i)) at 1.
  unfold R.v6389, N.v6389.
  rewrite ?node_6388.
  rewrite !state_r302_nr_5F302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r302_nr_5F302 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6390 (s : N.State) (i : N.Inputs) :
  R.v6390 (state s) (inputs i) = Zmod.unsigned (N.v6390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6390 s i)) at 1.
  unfold R.v6390, N.v6390.
  rewrite !state_r282_nr_5F282.
  rewrite !state_r283_nr_5F283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r282_nr_5F282 s)).
  rewrite ?(bits.mod_to_Z (N.r283_nr_5F283 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6391 (s : N.State) (i : N.Inputs) :
  R.v6391 (state s) (inputs i) = Zmod.unsigned (N.v6391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6391 s i)) at 1.
  unfold R.v6391, N.v6391.
  rewrite ?node_6310.
  rewrite !state_r284_nr_5F284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r284_nr_5F284 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6392 (s : N.State) (i : N.Inputs) :
  R.v6392 (state s) (inputs i) = Zmod.unsigned (N.v6392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6392 s i)) at 1.
  unfold R.v6392, N.v6392.
  rewrite ?node_6390.
  rewrite ?node_6391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6393 (s : N.State) (i : N.Inputs) :
  R.v6393 (state s) (inputs i) = Zmod.unsigned (N.v6393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6393 s i)) at 1.
  unfold R.v6393, N.v6393.
  rewrite ?node_6389.
  rewrite ?node_6392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6394 (s : N.State) (i : N.Inputs) :
  R.v6394 (state s) (inputs i) = Zmod.unsigned (N.v6394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6394 s i)) at 1.
  unfold R.v6394, N.v6394.
  rewrite ?node_6386.
  rewrite ?node_6393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6395 (s : N.State) (i : N.Inputs) :
  R.v6395 (state s) (inputs i) = Zmod.unsigned (N.v6395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6395 s i)) at 1.
  unfold R.v6395, N.v6395.
  rewrite ?node_6293.
  rewrite ?node_6300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6396 (s : N.State) (i : N.Inputs) :
  R.v6396 (state s) (inputs i) = Zmod.unsigned (N.v6396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6396 s i)) at 1.
  unfold R.v6396, N.v6396.
  rewrite ?node_6301.
  rewrite ?node_6308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6397 (s : N.State) (i : N.Inputs) :
  R.v6397 (state s) (inputs i) = Zmod.unsigned (N.v6397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6397 s i)) at 1.
  unfold R.v6397, N.v6397.
  rewrite ?node_6395.
  rewrite ?node_6396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6398 (s : N.State) (i : N.Inputs) :
  R.v6398 (state s) (inputs i) = Zmod.unsigned (N.v6398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6398 s i)) at 1.
  unfold R.v6398, N.v6398.
  rewrite ?node_6394.
  rewrite ?node_6397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6399 (s : N.State) (i : N.Inputs) :
  R.v6399 (state s) (inputs i) = Zmod.unsigned (N.v6399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6399 s i)) at 1.
  unfold R.v6399, N.v6399.
  rewrite ?node_6288.
  rewrite !state_r273_nr_5F273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r273_nr_5F273 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6400 (s : N.State) (i : N.Inputs) :
  R.v6400 (state s) (inputs i) = Zmod.unsigned (N.v6400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6400 s i)) at 1.
  unfold R.v6400, N.v6400.
  rewrite ?node_6289.
  rewrite ?node_6292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6401 (s : N.State) (i : N.Inputs) :
  R.v6401 (state s) (inputs i) = Zmod.unsigned (N.v6401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6401 s i)) at 1.
  unfold R.v6401, N.v6401.
  rewrite ?node_6399.
  rewrite ?node_6400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6402 (s : N.State) (i : N.Inputs) :
  R.v6402 (state s) (inputs i) = Zmod.unsigned (N.v6402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6402 s i)) at 1.
  unfold R.v6402, N.v6402.
  rewrite ?node_6401.
  rewrite !state_r303_nr_5F303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r303_nr_5F303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6403 (s : N.State) (i : N.Inputs) :
  R.v6403 (state s) (inputs i) = Zmod.unsigned (N.v6403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6403 s i)) at 1.
  unfold R.v6403, N.v6403.
  rewrite ?node_6295.
  rewrite !state_r277_nr_5F277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r277_nr_5F277 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6404 (s : N.State) (i : N.Inputs) :
  R.v6404 (state s) (inputs i) = Zmod.unsigned (N.v6404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6404 s i)) at 1.
  unfold R.v6404, N.v6404.
  rewrite ?node_6296.
  rewrite ?node_6299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6405 (s : N.State) (i : N.Inputs) :
  R.v6405 (state s) (inputs i) = Zmod.unsigned (N.v6405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6405 s i)) at 1.
  unfold R.v6405, N.v6405.
  rewrite ?node_6403.
  rewrite ?node_6404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6406 (s : N.State) (i : N.Inputs) :
  R.v6406 (state s) (inputs i) = Zmod.unsigned (N.v6406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6406 s i)) at 1.
  unfold R.v6406, N.v6406.
  rewrite ?node_6402.
  rewrite ?node_6405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6407 (s : N.State) (i : N.Inputs) :
  R.v6407 (state s) (inputs i) = Zmod.unsigned (N.v6407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6407 s i)) at 1.
  unfold R.v6407, N.v6407.
  rewrite ?node_6303.
  rewrite !state_r281_nr_5F281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r281_nr_5F281 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6408 (s : N.State) (i : N.Inputs) :
  R.v6408 (state s) (inputs i) = Zmod.unsigned (N.v6408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6408 s i)) at 1.
  unfold R.v6408, N.v6408.
  rewrite ?node_6304.
  rewrite ?node_6307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6409 (s : N.State) (i : N.Inputs) :
  R.v6409 (state s) (inputs i) = Zmod.unsigned (N.v6409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6409 s i)) at 1.
  unfold R.v6409, N.v6409.
  rewrite ?node_6407.
  rewrite ?node_6408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6410 (s : N.State) (i : N.Inputs) :
  R.v6410 (state s) (inputs i) = Zmod.unsigned (N.v6410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6410 s i)) at 1.
  unfold R.v6410, N.v6410.
  rewrite ?node_6406.
  rewrite ?node_6409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6411 (s : N.State) (i : N.Inputs) :
  R.v6411 (state s) (inputs i) = Zmod.unsigned (N.v6411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6411 s i)) at 1.
  unfold R.v6411, N.v6411.
  rewrite ?node_6324.
  rewrite !state_r286_nr_5F286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r286_nr_5F286 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6412 (s : N.State) (i : N.Inputs) :
  R.v6412 (state s) (inputs i) = Zmod.unsigned (N.v6412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6412 s i)) at 1.
  unfold R.v6412, N.v6412.
  rewrite ?node_6325.
  rewrite ?node_6328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6413 (s : N.State) (i : N.Inputs) :
  R.v6413 (state s) (inputs i) = Zmod.unsigned (N.v6413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6413 s i)) at 1.
  unfold R.v6413, N.v6413.
  rewrite ?node_6411.
  rewrite ?node_6412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6414 (s : N.State) (i : N.Inputs) :
  R.v6414 (state s) (inputs i) = Zmod.unsigned (N.v6414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6414 s i)) at 1.
  unfold R.v6414, N.v6414.
  rewrite ?node_6410.
  rewrite ?node_6413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6415 (s : N.State) (i : N.Inputs) :
  R.v6415 (state s) (inputs i) = Zmod.unsigned (N.v6415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6415 s i)) at 1.
  unfold R.v6415, N.v6415.
  rewrite ?node_6398.
  rewrite ?node_6414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6416 (s : N.State) (i : N.Inputs) :
  R.v6416 (state s) (inputs i) = Zmod.unsigned (N.v6416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6416 s i)) at 1.
  unfold R.v6416, N.v6416.
  rewrite ?node_6311.
  rewrite !state_r285_nr_5F285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r285_nr_5F285 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6417 (s : N.State) (i : N.Inputs) :
  R.v6417 (state s) (inputs i) = Zmod.unsigned (N.v6417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6417 s i)) at 1.
  unfold R.v6417, N.v6417.
  rewrite ?node_6312.
  rewrite ?node_6315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6418 (s : N.State) (i : N.Inputs) :
  R.v6418 (state s) (inputs i) = Zmod.unsigned (N.v6418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6418 s i)) at 1.
  unfold R.v6418, N.v6418.
  rewrite ?node_6416.
  rewrite ?node_6417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6419 (s : N.State) (i : N.Inputs) :
  R.v6419 (state s) (inputs i) = Zmod.unsigned (N.v6419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6419 s i)) at 1.
  unfold R.v6419, N.v6419.
  rewrite ?node_6415.
  rewrite ?node_6418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6420 (s : N.State) (i : N.Inputs) :
  R.v6420 (state s) (inputs i) = Zmod.unsigned (N.v6420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6420 s i)) at 1.
  unfold R.v6420, N.v6420.
  rewrite ?node_6309.
  rewrite ?node_6316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6421 (s : N.State) (i : N.Inputs) :
  R.v6421 (state s) (inputs i) = Zmod.unsigned (N.v6421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6421 s i)) at 1.
  unfold R.v6421, N.v6421.
  rewrite ?node_6317.
  rewrite ?node_6320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6422 (s : N.State) (i : N.Inputs) :
  R.v6422 (state s) (inputs i) = Zmod.unsigned (N.v6422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6422 s i)) at 1.
  unfold R.v6422, N.v6422.
  rewrite ?node_6420.
  rewrite ?node_6421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6423 (s : N.State) (i : N.Inputs) :
  R.v6423 (state s) (inputs i) = Zmod.unsigned (N.v6423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6423 s i)) at 1.
  unfold R.v6423, N.v6423.
  rewrite ?node_6419.
  rewrite ?node_6422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6424 (s : N.State) (i : N.Inputs) :
  R.v6424 (state s) (inputs i) = Zmod.unsigned (N.v6424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6424 s i)) at 1.
  unfold R.v6424, N.v6424.
  rewrite ?node_6321.
  rewrite ?node_6337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6425 (s : N.State) (i : N.Inputs) :
  R.v6425 (state s) (inputs i) = Zmod.unsigned (N.v6425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6425 s i)) at 1.
  unfold R.v6425, N.v6425.
  rewrite ?node_6338.
  rewrite ?node_6341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6426 (s : N.State) (i : N.Inputs) :
  R.v6426 (state s) (inputs i) = Zmod.unsigned (N.v6426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6426 s i)) at 1.
  unfold R.v6426, N.v6426.
  rewrite ?node_6424.
  rewrite ?node_6425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6427 (s : N.State) (i : N.Inputs) :
  R.v6427 (state s) (inputs i) = Zmod.unsigned (N.v6427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6427 s i)) at 1.
  unfold R.v6427, N.v6427.
  rewrite ?node_6423.
  rewrite ?node_6426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6428 (s : N.State) (i : N.Inputs) :
  R.v6428 (state s) (inputs i) = Zmod.unsigned (N.v6428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6428 s i)) at 1.
  unfold R.v6428, N.v6428.
  rewrite ?node_6329.
  rewrite ?node_6332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6429 (s : N.State) (i : N.Inputs) :
  R.v6429 (state s) (inputs i) = Zmod.unsigned (N.v6429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6429 s i)) at 1.
  unfold R.v6429, N.v6429.
  rewrite ?node_6333.
  rewrite ?node_6336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6430 (s : N.State) (i : N.Inputs) :
  R.v6430 (state s) (inputs i) = Zmod.unsigned (N.v6430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6430 s i)) at 1.
  unfold R.v6430, N.v6430.
  rewrite ?node_6428.
  rewrite ?node_6429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6431 (s : N.State) (i : N.Inputs) :
  R.v6431 (state s) (inputs i) = Zmod.unsigned (N.v6431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6431 s i)) at 1.
  unfold R.v6431, N.v6431.
  rewrite ?node_6427.
  rewrite ?node_6430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6432 (s : N.State) (i : N.Inputs) :
  R.v6432 (state s) (inputs i) = Zmod.unsigned (N.v6432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6432 s i)) at 1.
  unfold R.v6432, N.v6432.
  rewrite ?node_6342.
  rewrite ?node_6345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6433 (s : N.State) (i : N.Inputs) :
  R.v6433 (state s) (inputs i) = Zmod.unsigned (N.v6433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6433 s i)) at 1.
  unfold R.v6433, N.v6433.
  rewrite ?node_6346.
  rewrite ?node_6349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6434 (s : N.State) (i : N.Inputs) :
  R.v6434 (state s) (inputs i) = Zmod.unsigned (N.v6434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6434 s i)) at 1.
  unfold R.v6434, N.v6434.
  rewrite ?node_6432.
  rewrite ?node_6433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6435 (s : N.State) (i : N.Inputs) :
  R.v6435 (state s) (inputs i) = Zmod.unsigned (N.v6435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6435 s i)) at 1.
  unfold R.v6435, N.v6435.
  rewrite ?node_6431.
  rewrite ?node_6434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6436 (s : N.State) (i : N.Inputs) :
  R.v6436 (state s) (inputs i) = Zmod.unsigned (N.v6436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6436 s i)) at 1.
  unfold R.v6436, N.v6436.
  rewrite ?node_6350.
  rewrite ?node_6353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6437 (s : N.State) (i : N.Inputs) :
  R.v6437 (state s) (inputs i) = Zmod.unsigned (N.v6437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6437 s i)) at 1.
  unfold R.v6437, N.v6437.
  rewrite ?node_6354.
  rewrite ?node_6357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6438 (s : N.State) (i : N.Inputs) :
  R.v6438 (state s) (inputs i) = Zmod.unsigned (N.v6438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6438 s i)) at 1.
  unfold R.v6438, N.v6438.
  rewrite ?node_6436.
  rewrite ?node_6437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6439 (s : N.State) (i : N.Inputs) :
  R.v6439 (state s) (inputs i) = Zmod.unsigned (N.v6439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6439 s i)) at 1.
  unfold R.v6439, N.v6439.
  rewrite ?node_6435.
  rewrite ?node_6438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6440 (s : N.State) (i : N.Inputs) :
  R.v6440 (state s) (inputs i) = Zmod.unsigned (N.v6440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6440 s i)) at 1.
  unfold R.v6440, N.v6440.
  rewrite ?node_6439.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2335_nr_5F2366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2335_nr_5F2366 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6441 (s : N.State) (i : N.Inputs) :
  R.v6441 (state s) (inputs i) = Zmod.unsigned (N.v6441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6441 s i)) at 1.
  unfold R.v6441, N.v6441.
  rewrite ?node_6358.
  rewrite ?node_6359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6442 (s : N.State) (i : N.Inputs) :
  R.v6442 (state s) (inputs i) = Zmod.unsigned (N.v6442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6442 s i)) at 1.
  unfold R.v6442, N.v6442.
  rewrite ?node_6441.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2336_nr_5F2367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2336_nr_5F2367 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6443 (s : N.State) (i : N.Inputs) :
  R.v6443 (state s) (inputs i) = Zmod.unsigned (N.v6443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6443 s i)) at 1.
  unfold R.v6443, N.v6443.
  rewrite !state_r304_nr_5F304.
  rewrite !state_r305_nr_5F305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r304_nr_5F304 s)).
  rewrite ?(bits.mod_to_Z (N.r305_nr_5F305 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6444 (s : N.State) (i : N.Inputs) :
  R.v6444 (state s) (inputs i) = Zmod.unsigned (N.v6444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6444 s i)) at 1.
  unfold R.v6444, N.v6444.
  rewrite ?node_6443.
  rewrite !state_r306_nr_5F306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r306_nr_5F306 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6445 (s : N.State) (i : N.Inputs) :
  R.v6445 (state s) (inputs i) = Zmod.unsigned (N.v6445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6445 s i)) at 1.
  unfold R.v6445, N.v6445.
  rewrite ?node_6444.
  rewrite !state_r307_nr_5F307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r307_nr_5F307 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6446 (s : N.State) (i : N.Inputs) :
  R.v6446 (state s) (inputs i) = Zmod.unsigned (N.v6446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6446 s i)) at 1.
  unfold R.v6446, N.v6446.
  rewrite !state_r287_nr_5F287.
  rewrite !state_r288_nr_5F288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r287_nr_5F287 s)).
  rewrite ?(bits.mod_to_Z (N.r288_nr_5F288 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6447 (s : N.State) (i : N.Inputs) :
  R.v6447 (state s) (inputs i) = Zmod.unsigned (N.v6447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6447 s i)) at 1.
  unfold R.v6447, N.v6447.
  rewrite ?node_6364.
  rewrite !state_r289_nr_5F289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r289_nr_5F289 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6448 (s : N.State) (i : N.Inputs) :
  R.v6448 (state s) (inputs i) = Zmod.unsigned (N.v6448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6448 s i)) at 1.
  unfold R.v6448, N.v6448.
  rewrite ?node_6446.
  rewrite ?node_6447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6449 (s : N.State) (i : N.Inputs) :
  R.v6449 (state s) (inputs i) = Zmod.unsigned (N.v6449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6449 s i)) at 1.
  unfold R.v6449, N.v6449.
  rewrite ?node_6445.
  rewrite ?node_6448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6450 (s : N.State) (i : N.Inputs) :
  R.v6450 (state s) (inputs i) = Zmod.unsigned (N.v6450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6450 s i)) at 1.
  unfold R.v6450, N.v6450.
  rewrite !state_r308_nr_5F308.
  rewrite !state_r309_nr_5F309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r308_nr_5F308 s)).
  rewrite ?(bits.mod_to_Z (N.r309_nr_5F309 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6451 (s : N.State) (i : N.Inputs) :
  R.v6451 (state s) (inputs i) = Zmod.unsigned (N.v6451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6451 s i)) at 1.
  unfold R.v6451, N.v6451.
  rewrite ?node_6450.
  rewrite !state_r310_nr_5F310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r310_nr_5F310 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6452 (s : N.State) (i : N.Inputs) :
  R.v6452 (state s) (inputs i) = Zmod.unsigned (N.v6452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6452 s i)) at 1.
  unfold R.v6452, N.v6452.
  rewrite ?node_6451.
  rewrite !state_r311_nr_5F311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r311_nr_5F311 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6453 (s : N.State) (i : N.Inputs) :
  R.v6453 (state s) (inputs i) = Zmod.unsigned (N.v6453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6453 s i)) at 1.
  unfold R.v6453, N.v6453.
  rewrite !state_r291_nr_5F291.
  rewrite !state_r292_nr_5F292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r291_nr_5F291 s)).
  rewrite ?(bits.mod_to_Z (N.r292_nr_5F292 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6454 (s : N.State) (i : N.Inputs) :
  R.v6454 (state s) (inputs i) = Zmod.unsigned (N.v6454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6454 s i)) at 1.
  unfold R.v6454, N.v6454.
  rewrite ?node_6371.
  rewrite !state_r293_nr_5F293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r293_nr_5F293 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6455 (s : N.State) (i : N.Inputs) :
  R.v6455 (state s) (inputs i) = Zmod.unsigned (N.v6455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6455 s i)) at 1.
  unfold R.v6455, N.v6455.
  rewrite ?node_6453.
  rewrite ?node_6454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6456 (s : N.State) (i : N.Inputs) :
  R.v6456 (state s) (inputs i) = Zmod.unsigned (N.v6456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6456 s i)) at 1.
  unfold R.v6456, N.v6456.
  rewrite ?node_6452.
  rewrite ?node_6455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6457 (s : N.State) (i : N.Inputs) :
  R.v6457 (state s) (inputs i) = Zmod.unsigned (N.v6457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6457 s i)) at 1.
  unfold R.v6457, N.v6457.
  rewrite ?node_6449.
  rewrite ?node_6456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6458 (s : N.State) (i : N.Inputs) :
  R.v6458 (state s) (inputs i) = Zmod.unsigned (N.v6458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6458 s i)) at 1.
  unfold R.v6458, N.v6458.
  rewrite !state_r312_nr_5F312.
  rewrite !state_r313_nr_5F313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r312_nr_5F312 s)).
  rewrite ?(bits.mod_to_Z (N.r313_nr_5F313 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6459 (s : N.State) (i : N.Inputs) :
  R.v6459 (state s) (inputs i) = Zmod.unsigned (N.v6459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6459 s i)) at 1.
  unfold R.v6459, N.v6459.
  rewrite ?node_6458.
  rewrite !state_r314_nr_5F314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r314_nr_5F314 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6460 (s : N.State) (i : N.Inputs) :
  R.v6460 (state s) (inputs i) = Zmod.unsigned (N.v6460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6460 s i)) at 1.
  unfold R.v6460, N.v6460.
  rewrite ?node_6459.
  rewrite !state_r315_nr_5F315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r315_nr_5F315 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6461 (s : N.State) (i : N.Inputs) :
  R.v6461 (state s) (inputs i) = Zmod.unsigned (N.v6461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6461 s i)) at 1.
  unfold R.v6461, N.v6461.
  rewrite !state_r295_nr_5F295.
  rewrite !state_r296_nr_5F296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r295_nr_5F295 s)).
  rewrite ?(bits.mod_to_Z (N.r296_nr_5F296 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6462 (s : N.State) (i : N.Inputs) :
  R.v6462 (state s) (inputs i) = Zmod.unsigned (N.v6462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6462 s i)) at 1.
  unfold R.v6462, N.v6462.
  rewrite ?node_6379.
  rewrite !state_r297_nr_5F297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r297_nr_5F297 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6463 (s : N.State) (i : N.Inputs) :
  R.v6463 (state s) (inputs i) = Zmod.unsigned (N.v6463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6463 s i)) at 1.
  unfold R.v6463, N.v6463.
  rewrite ?node_6461.
  rewrite ?node_6462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6464 (s : N.State) (i : N.Inputs) :
  R.v6464 (state s) (inputs i) = Zmod.unsigned (N.v6464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6464 s i)) at 1.
  unfold R.v6464, N.v6464.
  rewrite ?node_6460.
  rewrite ?node_6463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6465 (s : N.State) (i : N.Inputs) :
  R.v6465 (state s) (inputs i) = Zmod.unsigned (N.v6465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6465 s i)) at 1.
  unfold R.v6465, N.v6465.
  rewrite ?node_6457.
  rewrite ?node_6464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6466 (s : N.State) (i : N.Inputs) :
  R.v6466 (state s) (inputs i) = Zmod.unsigned (N.v6466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6466 s i)) at 1.
  unfold R.v6466, N.v6466.
  rewrite !state_r316_nr_5F316.
  rewrite !state_r317_nr_5F317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r316_nr_5F316 s)).
  rewrite ?(bits.mod_to_Z (N.r317_nr_5F317 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6467 (s : N.State) (i : N.Inputs) :
  R.v6467 (state s) (inputs i) = Zmod.unsigned (N.v6467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6467 s i)) at 1.
  unfold R.v6467, N.v6467.
  rewrite ?node_6466.
  rewrite !state_r318_nr_5F318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r318_nr_5F318 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6468 (s : N.State) (i : N.Inputs) :
  R.v6468 (state s) (inputs i) = Zmod.unsigned (N.v6468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6468 s i)) at 1.
  unfold R.v6468, N.v6468.
  rewrite ?node_6467.
  rewrite !state_r319_nr_5F319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r319_nr_5F319 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6469 (s : N.State) (i : N.Inputs) :
  R.v6469 (state s) (inputs i) = Zmod.unsigned (N.v6469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6469 s i)) at 1.
  unfold R.v6469, N.v6469.
  rewrite !state_r299_nr_5F299.
  rewrite !state_r300_nr_5F300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r299_nr_5F299 s)).
  rewrite ?(bits.mod_to_Z (N.r300_nr_5F300 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6470 (s : N.State) (i : N.Inputs) :
  R.v6470 (state s) (inputs i) = Zmod.unsigned (N.v6470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6470 s i)) at 1.
  unfold R.v6470, N.v6470.
  rewrite ?node_6387.
  rewrite !state_r301_nr_5F301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r301_nr_5F301 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6471 (s : N.State) (i : N.Inputs) :
  R.v6471 (state s) (inputs i) = Zmod.unsigned (N.v6471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6471 s i)) at 1.
  unfold R.v6471, N.v6471.
  rewrite ?node_6469.
  rewrite ?node_6470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6472 (s : N.State) (i : N.Inputs) :
  R.v6472 (state s) (inputs i) = Zmod.unsigned (N.v6472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6472 s i)) at 1.
  unfold R.v6472, N.v6472.
  rewrite ?node_6468.
  rewrite ?node_6471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6473 (s : N.State) (i : N.Inputs) :
  R.v6473 (state s) (inputs i) = Zmod.unsigned (N.v6473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6473 s i)) at 1.
  unfold R.v6473, N.v6473.
  rewrite ?node_6465.
  rewrite ?node_6472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6474 (s : N.State) (i : N.Inputs) :
  R.v6474 (state s) (inputs i) = Zmod.unsigned (N.v6474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6474 s i)) at 1.
  unfold R.v6474, N.v6474.
  rewrite ?node_6370.
  rewrite ?node_6377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6475 (s : N.State) (i : N.Inputs) :
  R.v6475 (state s) (inputs i) = Zmod.unsigned (N.v6475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6475 s i)) at 1.
  unfold R.v6475, N.v6475.
  rewrite ?node_6378.
  rewrite ?node_6385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6476 (s : N.State) (i : N.Inputs) :
  R.v6476 (state s) (inputs i) = Zmod.unsigned (N.v6476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6476 s i)) at 1.
  unfold R.v6476, N.v6476.
  rewrite ?node_6474.
  rewrite ?node_6475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6477 (s : N.State) (i : N.Inputs) :
  R.v6477 (state s) (inputs i) = Zmod.unsigned (N.v6477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6477 s i)) at 1.
  unfold R.v6477, N.v6477.
  rewrite ?node_6473.
  rewrite ?node_6476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6478 (s : N.State) (i : N.Inputs) :
  R.v6478 (state s) (inputs i) = Zmod.unsigned (N.v6478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6478 s i)) at 1.
  unfold R.v6478, N.v6478.
  rewrite !state_r320_nr_5F320.
  rewrite !state_r321_nr_5F321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r320_nr_5F320 s)).
  rewrite ?(bits.mod_to_Z (N.r321_nr_5F321 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6479 (s : N.State) (i : N.Inputs) :
  R.v6479 (state s) (inputs i) = Zmod.unsigned (N.v6479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6479 s i)) at 1.
  unfold R.v6479, N.v6479.
  rewrite ?node_6365.
  rewrite !state_r290_nr_5F290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r290_nr_5F290 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6480 (s : N.State) (i : N.Inputs) :
  R.v6480 (state s) (inputs i) = Zmod.unsigned (N.v6480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6480 s i)) at 1.
  unfold R.v6480, N.v6480.
  rewrite ?node_6366.
  rewrite ?node_6369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6481 (s : N.State) (i : N.Inputs) :
  R.v6481 (state s) (inputs i) = Zmod.unsigned (N.v6481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6481 s i)) at 1.
  unfold R.v6481, N.v6481.
  rewrite ?node_6479.
  rewrite ?node_6480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6482 (s : N.State) (i : N.Inputs) :
  R.v6482 (state s) (inputs i) = Zmod.unsigned (N.v6482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6482 s i)) at 1.
  unfold R.v6482, N.v6482.
  rewrite ?node_6478.
  rewrite ?node_6481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6483 (s : N.State) (i : N.Inputs) :
  R.v6483 (state s) (inputs i) = Zmod.unsigned (N.v6483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6483 s i)) at 1.
  unfold R.v6483, N.v6483.
  rewrite ?node_6372.
  rewrite !state_r294_nr_5F294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r294_nr_5F294 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6484 (s : N.State) (i : N.Inputs) :
  R.v6484 (state s) (inputs i) = Zmod.unsigned (N.v6484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6484 s i)) at 1.
  unfold R.v6484, N.v6484.
  rewrite ?node_6373.
  rewrite ?node_6376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6485 (s : N.State) (i : N.Inputs) :
  R.v6485 (state s) (inputs i) = Zmod.unsigned (N.v6485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6485 s i)) at 1.
  unfold R.v6485, N.v6485.
  rewrite ?node_6483.
  rewrite ?node_6484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6486 (s : N.State) (i : N.Inputs) :
  R.v6486 (state s) (inputs i) = Zmod.unsigned (N.v6486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6486 s i)) at 1.
  unfold R.v6486, N.v6486.
  rewrite ?node_6482.
  rewrite ?node_6485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6487 (s : N.State) (i : N.Inputs) :
  R.v6487 (state s) (inputs i) = Zmod.unsigned (N.v6487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6487 s i)) at 1.
  unfold R.v6487, N.v6487.
  rewrite ?node_6380.
  rewrite !state_r298_nr_5F298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r298_nr_5F298 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6488 (s : N.State) (i : N.Inputs) :
  R.v6488 (state s) (inputs i) = Zmod.unsigned (N.v6488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6488 s i)) at 1.
  unfold R.v6488, N.v6488.
  rewrite ?node_6381.
  rewrite ?node_6384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6489 (s : N.State) (i : N.Inputs) :
  R.v6489 (state s) (inputs i) = Zmod.unsigned (N.v6489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6489 s i)) at 1.
  unfold R.v6489, N.v6489.
  rewrite ?node_6487.
  rewrite ?node_6488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6490 (s : N.State) (i : N.Inputs) :
  R.v6490 (state s) (inputs i) = Zmod.unsigned (N.v6490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6490 s i)) at 1.
  unfold R.v6490, N.v6490.
  rewrite ?node_6486.
  rewrite ?node_6489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6491 (s : N.State) (i : N.Inputs) :
  R.v6491 (state s) (inputs i) = Zmod.unsigned (N.v6491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6491 s i)) at 1.
  unfold R.v6491, N.v6491.
  rewrite ?node_6401.
  rewrite !state_r303_nr_5F303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r303_nr_5F303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6492 (s : N.State) (i : N.Inputs) :
  R.v6492 (state s) (inputs i) = Zmod.unsigned (N.v6492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6492 s i)) at 1.
  unfold R.v6492, N.v6492.
  rewrite ?node_6402.
  rewrite ?node_6405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6493 (s : N.State) (i : N.Inputs) :
  R.v6493 (state s) (inputs i) = Zmod.unsigned (N.v6493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6493 s i)) at 1.
  unfold R.v6493, N.v6493.
  rewrite ?node_6491.
  rewrite ?node_6492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6494 (s : N.State) (i : N.Inputs) :
  R.v6494 (state s) (inputs i) = Zmod.unsigned (N.v6494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6494 s i)) at 1.
  unfold R.v6494, N.v6494.
  rewrite ?node_6490.
  rewrite ?node_6493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6495 (s : N.State) (i : N.Inputs) :
  R.v6495 (state s) (inputs i) = Zmod.unsigned (N.v6495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6495 s i)) at 1.
  unfold R.v6495, N.v6495.
  rewrite ?node_6477.
  rewrite ?node_6494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6496 (s : N.State) (i : N.Inputs) :
  R.v6496 (state s) (inputs i) = Zmod.unsigned (N.v6496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6496 s i)) at 1.
  unfold R.v6496, N.v6496.
  rewrite ?node_6388.
  rewrite !state_r302_nr_5F302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r302_nr_5F302 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6497 (s : N.State) (i : N.Inputs) :
  R.v6497 (state s) (inputs i) = Zmod.unsigned (N.v6497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6497 s i)) at 1.
  unfold R.v6497, N.v6497.
  rewrite ?node_6389.
  rewrite ?node_6392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6498 (s : N.State) (i : N.Inputs) :
  R.v6498 (state s) (inputs i) = Zmod.unsigned (N.v6498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6498 s i)) at 1.
  unfold R.v6498, N.v6498.
  rewrite ?node_6496.
  rewrite ?node_6497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6499 (s : N.State) (i : N.Inputs) :
  R.v6499 (state s) (inputs i) = Zmod.unsigned (N.v6499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6499 s i)) at 1.
  unfold R.v6499, N.v6499.
  rewrite ?node_6495.
  rewrite ?node_6498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6500 (s : N.State) (i : N.Inputs) :
  R.v6500 (state s) (inputs i) = Zmod.unsigned (N.v6500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6500 s i)) at 1.
  unfold R.v6500, N.v6500.
  rewrite ?node_6386.
  rewrite ?node_6393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6501 (s : N.State) (i : N.Inputs) :
  R.v6501 (state s) (inputs i) = Zmod.unsigned (N.v6501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6501 s i)) at 1.
  unfold R.v6501, N.v6501.
  rewrite ?node_6394.
  rewrite ?node_6397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6502 (s : N.State) (i : N.Inputs) :
  R.v6502 (state s) (inputs i) = Zmod.unsigned (N.v6502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6502 s i)) at 1.
  unfold R.v6502, N.v6502.
  rewrite ?node_6500.
  rewrite ?node_6501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6503 (s : N.State) (i : N.Inputs) :
  R.v6503 (state s) (inputs i) = Zmod.unsigned (N.v6503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6503 s i)) at 1.
  unfold R.v6503, N.v6503.
  rewrite ?node_6499.
  rewrite ?node_6502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6504 (s : N.State) (i : N.Inputs) :
  R.v6504 (state s) (inputs i) = Zmod.unsigned (N.v6504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6504 s i)) at 1.
  unfold R.v6504, N.v6504.
  rewrite ?node_6398.
  rewrite ?node_6414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6505 (s : N.State) (i : N.Inputs) :
  R.v6505 (state s) (inputs i) = Zmod.unsigned (N.v6505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6505 s i)) at 1.
  unfold R.v6505, N.v6505.
  rewrite ?node_6415.
  rewrite ?node_6418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6506 (s : N.State) (i : N.Inputs) :
  R.v6506 (state s) (inputs i) = Zmod.unsigned (N.v6506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6506 s i)) at 1.
  unfold R.v6506, N.v6506.
  rewrite ?node_6504.
  rewrite ?node_6505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6507 (s : N.State) (i : N.Inputs) :
  R.v6507 (state s) (inputs i) = Zmod.unsigned (N.v6507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6507 s i)) at 1.
  unfold R.v6507, N.v6507.
  rewrite ?node_6503.
  rewrite ?node_6506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6508 (s : N.State) (i : N.Inputs) :
  R.v6508 (state s) (inputs i) = Zmod.unsigned (N.v6508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6508 s i)) at 1.
  unfold R.v6508, N.v6508.
  rewrite ?node_6406.
  rewrite ?node_6409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6509 (s : N.State) (i : N.Inputs) :
  R.v6509 (state s) (inputs i) = Zmod.unsigned (N.v6509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6509 s i)) at 1.
  unfold R.v6509, N.v6509.
  rewrite ?node_6410.
  rewrite ?node_6413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6510 (s : N.State) (i : N.Inputs) :
  R.v6510 (state s) (inputs i) = Zmod.unsigned (N.v6510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6510 s i)) at 1.
  unfold R.v6510, N.v6510.
  rewrite ?node_6508.
  rewrite ?node_6509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6511 (s : N.State) (i : N.Inputs) :
  R.v6511 (state s) (inputs i) = Zmod.unsigned (N.v6511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6511 s i)) at 1.
  unfold R.v6511, N.v6511.
  rewrite ?node_6507.
  rewrite ?node_6510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6512 (s : N.State) (i : N.Inputs) :
  R.v6512 (state s) (inputs i) = Zmod.unsigned (N.v6512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6512 s i)) at 1.
  unfold R.v6512, N.v6512.
  rewrite ?node_6419.
  rewrite ?node_6422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6513 (s : N.State) (i : N.Inputs) :
  R.v6513 (state s) (inputs i) = Zmod.unsigned (N.v6513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6513 s i)) at 1.
  unfold R.v6513, N.v6513.
  rewrite ?node_6423.
  rewrite ?node_6426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6514 (s : N.State) (i : N.Inputs) :
  R.v6514 (state s) (inputs i) = Zmod.unsigned (N.v6514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6514 s i)) at 1.
  unfold R.v6514, N.v6514.
  rewrite ?node_6512.
  rewrite ?node_6513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6515 (s : N.State) (i : N.Inputs) :
  R.v6515 (state s) (inputs i) = Zmod.unsigned (N.v6515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6515 s i)) at 1.
  unfold R.v6515, N.v6515.
  rewrite ?node_6511.
  rewrite ?node_6514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6516 (s : N.State) (i : N.Inputs) :
  R.v6516 (state s) (inputs i) = Zmod.unsigned (N.v6516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6516 s i)) at 1.
  unfold R.v6516, N.v6516.
  rewrite ?node_6427.
  rewrite ?node_6430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6517 (s : N.State) (i : N.Inputs) :
  R.v6517 (state s) (inputs i) = Zmod.unsigned (N.v6517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6517 s i)) at 1.
  unfold R.v6517, N.v6517.
  rewrite ?node_6431.
  rewrite ?node_6434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6518 (s : N.State) (i : N.Inputs) :
  R.v6518 (state s) (inputs i) = Zmod.unsigned (N.v6518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6518 s i)) at 1.
  unfold R.v6518, N.v6518.
  rewrite ?node_6516.
  rewrite ?node_6517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6519 (s : N.State) (i : N.Inputs) :
  R.v6519 (state s) (inputs i) = Zmod.unsigned (N.v6519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6519 s i)) at 1.
  unfold R.v6519, N.v6519.
  rewrite ?node_6515.
  rewrite ?node_6518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6520 (s : N.State) (i : N.Inputs) :
  R.v6520 (state s) (inputs i) = Zmod.unsigned (N.v6520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6520 s i)) at 1.
  unfold R.v6520, N.v6520.
  rewrite ?node_6519.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2337_nr_5F2368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2337_nr_5F2368 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6521 (s : N.State) (i : N.Inputs) :
  R.v6521 (state s) (inputs i) = Zmod.unsigned (N.v6521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6521 s i)) at 1.
  unfold R.v6521, N.v6521.
  rewrite ?node_6435.
  rewrite ?node_6438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6522 (s : N.State) (i : N.Inputs) :
  R.v6522 (state s) (inputs i) = Zmod.unsigned (N.v6522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6522 s i)) at 1.
  unfold R.v6522, N.v6522.
  rewrite ?node_6521.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2338_nr_5F2369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2338_nr_5F2369 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6523 (s : N.State) (i : N.Inputs) :
  R.v6523 (state s) (inputs i) = Zmod.unsigned (N.v6523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6523 s i)) at 1.
  unfold R.v6523, N.v6523.
  rewrite !state_r322_nr_5F322.
  rewrite !state_r323_nr_5F323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r322_nr_5F322 s)).
  rewrite ?(bits.mod_to_Z (N.r323_nr_5F323 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6524 (s : N.State) (i : N.Inputs) :
  R.v6524 (state s) (inputs i) = Zmod.unsigned (N.v6524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6524 s i)) at 1.
  unfold R.v6524, N.v6524.
  rewrite ?node_6523.
  rewrite !state_r324_nr_5F324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r324_nr_5F324 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6525 (s : N.State) (i : N.Inputs) :
  R.v6525 (state s) (inputs i) = Zmod.unsigned (N.v6525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6525 s i)) at 1.
  unfold R.v6525, N.v6525.
  rewrite ?node_6524.
  rewrite !state_r325_nr_5F325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r325_nr_5F325 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6526 (s : N.State) (i : N.Inputs) :
  R.v6526 (state s) (inputs i) = Zmod.unsigned (N.v6526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6526 s i)) at 1.
  unfold R.v6526, N.v6526.
  rewrite !state_r304_nr_5F304.
  rewrite !state_r305_nr_5F305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r304_nr_5F304 s)).
  rewrite ?(bits.mod_to_Z (N.r305_nr_5F305 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6527 (s : N.State) (i : N.Inputs) :
  R.v6527 (state s) (inputs i) = Zmod.unsigned (N.v6527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6527 s i)) at 1.
  unfold R.v6527, N.v6527.
  rewrite ?node_6443.
  rewrite !state_r306_nr_5F306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r306_nr_5F306 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6528 (s : N.State) (i : N.Inputs) :
  R.v6528 (state s) (inputs i) = Zmod.unsigned (N.v6528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6528 s i)) at 1.
  unfold R.v6528, N.v6528.
  rewrite ?node_6526.
  rewrite ?node_6527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6529 (s : N.State) (i : N.Inputs) :
  R.v6529 (state s) (inputs i) = Zmod.unsigned (N.v6529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6529 s i)) at 1.
  unfold R.v6529, N.v6529.
  rewrite ?node_6525.
  rewrite ?node_6528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6530 (s : N.State) (i : N.Inputs) :
  R.v6530 (state s) (inputs i) = Zmod.unsigned (N.v6530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6530 s i)) at 1.
  unfold R.v6530, N.v6530.
  rewrite !state_r326_nr_5F326.
  rewrite !state_r327_nr_5F327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r326_nr_5F326 s)).
  rewrite ?(bits.mod_to_Z (N.r327_nr_5F327 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6531 (s : N.State) (i : N.Inputs) :
  R.v6531 (state s) (inputs i) = Zmod.unsigned (N.v6531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6531 s i)) at 1.
  unfold R.v6531, N.v6531.
  rewrite ?node_6530.
  rewrite !state_r328_nr_5F328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r328_nr_5F328 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6532 (s : N.State) (i : N.Inputs) :
  R.v6532 (state s) (inputs i) = Zmod.unsigned (N.v6532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6532 s i)) at 1.
  unfold R.v6532, N.v6532.
  rewrite ?node_6531.
  rewrite !state_r329_nr_5F329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r329_nr_5F329 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6533 (s : N.State) (i : N.Inputs) :
  R.v6533 (state s) (inputs i) = Zmod.unsigned (N.v6533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6533 s i)) at 1.
  unfold R.v6533, N.v6533.
  rewrite !state_r308_nr_5F308.
  rewrite !state_r309_nr_5F309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r308_nr_5F308 s)).
  rewrite ?(bits.mod_to_Z (N.r309_nr_5F309 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6534 (s : N.State) (i : N.Inputs) :
  R.v6534 (state s) (inputs i) = Zmod.unsigned (N.v6534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6534 s i)) at 1.
  unfold R.v6534, N.v6534.
  rewrite ?node_6450.
  rewrite !state_r310_nr_5F310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r310_nr_5F310 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6535 (s : N.State) (i : N.Inputs) :
  R.v6535 (state s) (inputs i) = Zmod.unsigned (N.v6535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6535 s i)) at 1.
  unfold R.v6535, N.v6535.
  rewrite ?node_6533.
  rewrite ?node_6534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6536 (s : N.State) (i : N.Inputs) :
  R.v6536 (state s) (inputs i) = Zmod.unsigned (N.v6536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6536 s i)) at 1.
  unfold R.v6536, N.v6536.
  rewrite ?node_6532.
  rewrite ?node_6535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6537 (s : N.State) (i : N.Inputs) :
  R.v6537 (state s) (inputs i) = Zmod.unsigned (N.v6537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6537 s i)) at 1.
  unfold R.v6537, N.v6537.
  rewrite ?node_6529.
  rewrite ?node_6536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6538 (s : N.State) (i : N.Inputs) :
  R.v6538 (state s) (inputs i) = Zmod.unsigned (N.v6538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6538 s i)) at 1.
  unfold R.v6538, N.v6538.
  rewrite !state_r330_nr_5F330.
  rewrite !state_r331_nr_5F331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r330_nr_5F330 s)).
  rewrite ?(bits.mod_to_Z (N.r331_nr_5F331 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6539 (s : N.State) (i : N.Inputs) :
  R.v6539 (state s) (inputs i) = Zmod.unsigned (N.v6539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6539 s i)) at 1.
  unfold R.v6539, N.v6539.
  rewrite ?node_6538.
  rewrite !state_r332_nr_5F332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r332_nr_5F332 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6540 (s : N.State) (i : N.Inputs) :
  R.v6540 (state s) (inputs i) = Zmod.unsigned (N.v6540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6540 s i)) at 1.
  unfold R.v6540, N.v6540.
  rewrite ?node_6539.
  rewrite !state_r333_nr_5F333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r333_nr_5F333 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6541 (s : N.State) (i : N.Inputs) :
  R.v6541 (state s) (inputs i) = Zmod.unsigned (N.v6541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6541 s i)) at 1.
  unfold R.v6541, N.v6541.
  rewrite !state_r312_nr_5F312.
  rewrite !state_r313_nr_5F313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r312_nr_5F312 s)).
  rewrite ?(bits.mod_to_Z (N.r313_nr_5F313 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6542 (s : N.State) (i : N.Inputs) :
  R.v6542 (state s) (inputs i) = Zmod.unsigned (N.v6542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6542 s i)) at 1.
  unfold R.v6542, N.v6542.
  rewrite ?node_6458.
  rewrite !state_r314_nr_5F314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r314_nr_5F314 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6543 (s : N.State) (i : N.Inputs) :
  R.v6543 (state s) (inputs i) = Zmod.unsigned (N.v6543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6543 s i)) at 1.
  unfold R.v6543, N.v6543.
  rewrite ?node_6541.
  rewrite ?node_6542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6544 (s : N.State) (i : N.Inputs) :
  R.v6544 (state s) (inputs i) = Zmod.unsigned (N.v6544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6544 s i)) at 1.
  unfold R.v6544, N.v6544.
  rewrite ?node_6540.
  rewrite ?node_6543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6545 (s : N.State) (i : N.Inputs) :
  R.v6545 (state s) (inputs i) = Zmod.unsigned (N.v6545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6545 s i)) at 1.
  unfold R.v6545, N.v6545.
  rewrite ?node_6537.
  rewrite ?node_6544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6546 (s : N.State) (i : N.Inputs) :
  R.v6546 (state s) (inputs i) = Zmod.unsigned (N.v6546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6546 s i)) at 1.
  unfold R.v6546, N.v6546.
  rewrite !state_r334_nr_5F334.
  rewrite !state_r335_nr_5F335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r334_nr_5F334 s)).
  rewrite ?(bits.mod_to_Z (N.r335_nr_5F335 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6547 (s : N.State) (i : N.Inputs) :
  R.v6547 (state s) (inputs i) = Zmod.unsigned (N.v6547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6547 s i)) at 1.
  unfold R.v6547, N.v6547.
  rewrite ?node_6546.
  rewrite !state_r336_nr_5F336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r336_nr_5F336 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6548 (s : N.State) (i : N.Inputs) :
  R.v6548 (state s) (inputs i) = Zmod.unsigned (N.v6548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6548 s i)) at 1.
  unfold R.v6548, N.v6548.
  rewrite ?node_6547.
  rewrite !state_r337_nr_5F337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r337_nr_5F337 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6549 (s : N.State) (i : N.Inputs) :
  R.v6549 (state s) (inputs i) = Zmod.unsigned (N.v6549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6549 s i)) at 1.
  unfold R.v6549, N.v6549.
  rewrite !state_r316_nr_5F316.
  rewrite !state_r317_nr_5F317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r316_nr_5F316 s)).
  rewrite ?(bits.mod_to_Z (N.r317_nr_5F317 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6550 (s : N.State) (i : N.Inputs) :
  R.v6550 (state s) (inputs i) = Zmod.unsigned (N.v6550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6550 s i)) at 1.
  unfold R.v6550, N.v6550.
  rewrite ?node_6466.
  rewrite !state_r318_nr_5F318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r318_nr_5F318 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6551 (s : N.State) (i : N.Inputs) :
  R.v6551 (state s) (inputs i) = Zmod.unsigned (N.v6551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6551 s i)) at 1.
  unfold R.v6551, N.v6551.
  rewrite ?node_6549.
  rewrite ?node_6550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6552 (s : N.State) (i : N.Inputs) :
  R.v6552 (state s) (inputs i) = Zmod.unsigned (N.v6552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6552 s i)) at 1.
  unfold R.v6552, N.v6552.
  rewrite ?node_6548.
  rewrite ?node_6551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6553 (s : N.State) (i : N.Inputs) :
  R.v6553 (state s) (inputs i) = Zmod.unsigned (N.v6553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6553 s i)) at 1.
  unfold R.v6553, N.v6553.
  rewrite ?node_6545.
  rewrite ?node_6552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6554 (s : N.State) (i : N.Inputs) :
  R.v6554 (state s) (inputs i) = Zmod.unsigned (N.v6554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6554 s i)) at 1.
  unfold R.v6554, N.v6554.
  rewrite ?node_6449.
  rewrite ?node_6456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6555 (s : N.State) (i : N.Inputs) :
  R.v6555 (state s) (inputs i) = Zmod.unsigned (N.v6555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6555 s i)) at 1.
  unfold R.v6555, N.v6555.
  rewrite ?node_6457.
  rewrite ?node_6464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6556 (s : N.State) (i : N.Inputs) :
  R.v6556 (state s) (inputs i) = Zmod.unsigned (N.v6556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6556 s i)) at 1.
  unfold R.v6556, N.v6556.
  rewrite ?node_6554.
  rewrite ?node_6555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6557 (s : N.State) (i : N.Inputs) :
  R.v6557 (state s) (inputs i) = Zmod.unsigned (N.v6557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6557 s i)) at 1.
  unfold R.v6557, N.v6557.
  rewrite ?node_6553.
  rewrite ?node_6556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6558 (s : N.State) (i : N.Inputs) :
  R.v6558 (state s) (inputs i) = Zmod.unsigned (N.v6558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6558 s i)) at 1.
  unfold R.v6558, N.v6558.
  rewrite !state_r338_nr_5F338.
  rewrite !state_r339_nr_5F339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r338_nr_5F338 s)).
  rewrite ?(bits.mod_to_Z (N.r339_nr_5F339 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6559 (s : N.State) (i : N.Inputs) :
  R.v6559 (state s) (inputs i) = Zmod.unsigned (N.v6559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6559 s i)) at 1.
  unfold R.v6559, N.v6559.
  rewrite ?node_6444.
  rewrite !state_r307_nr_5F307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r307_nr_5F307 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6560 (s : N.State) (i : N.Inputs) :
  R.v6560 (state s) (inputs i) = Zmod.unsigned (N.v6560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6560 s i)) at 1.
  unfold R.v6560, N.v6560.
  rewrite ?node_6445.
  rewrite ?node_6448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6561 (s : N.State) (i : N.Inputs) :
  R.v6561 (state s) (inputs i) = Zmod.unsigned (N.v6561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6561 s i)) at 1.
  unfold R.v6561, N.v6561.
  rewrite ?node_6559.
  rewrite ?node_6560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6562 (s : N.State) (i : N.Inputs) :
  R.v6562 (state s) (inputs i) = Zmod.unsigned (N.v6562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6562 s i)) at 1.
  unfold R.v6562, N.v6562.
  rewrite ?node_6558.
  rewrite ?node_6561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6563 (s : N.State) (i : N.Inputs) :
  R.v6563 (state s) (inputs i) = Zmod.unsigned (N.v6563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6563 s i)) at 1.
  unfold R.v6563, N.v6563.
  rewrite ?node_6451.
  rewrite !state_r311_nr_5F311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r311_nr_5F311 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6564 (s : N.State) (i : N.Inputs) :
  R.v6564 (state s) (inputs i) = Zmod.unsigned (N.v6564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6564 s i)) at 1.
  unfold R.v6564, N.v6564.
  rewrite ?node_6452.
  rewrite ?node_6455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6565 (s : N.State) (i : N.Inputs) :
  R.v6565 (state s) (inputs i) = Zmod.unsigned (N.v6565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6565 s i)) at 1.
  unfold R.v6565, N.v6565.
  rewrite ?node_6563.
  rewrite ?node_6564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6566 (s : N.State) (i : N.Inputs) :
  R.v6566 (state s) (inputs i) = Zmod.unsigned (N.v6566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6566 s i)) at 1.
  unfold R.v6566, N.v6566.
  rewrite ?node_6562.
  rewrite ?node_6565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6567 (s : N.State) (i : N.Inputs) :
  R.v6567 (state s) (inputs i) = Zmod.unsigned (N.v6567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6567 s i)) at 1.
  unfold R.v6567, N.v6567.
  rewrite ?node_6459.
  rewrite !state_r315_nr_5F315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r315_nr_5F315 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6568 (s : N.State) (i : N.Inputs) :
  R.v6568 (state s) (inputs i) = Zmod.unsigned (N.v6568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6568 s i)) at 1.
  unfold R.v6568, N.v6568.
  rewrite ?node_6460.
  rewrite ?node_6463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6569 (s : N.State) (i : N.Inputs) :
  R.v6569 (state s) (inputs i) = Zmod.unsigned (N.v6569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6569 s i)) at 1.
  unfold R.v6569, N.v6569.
  rewrite ?node_6567.
  rewrite ?node_6568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6570 (s : N.State) (i : N.Inputs) :
  R.v6570 (state s) (inputs i) = Zmod.unsigned (N.v6570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6570 s i)) at 1.
  unfold R.v6570, N.v6570.
  rewrite ?node_6566.
  rewrite ?node_6569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6571 (s : N.State) (i : N.Inputs) :
  R.v6571 (state s) (inputs i) = Zmod.unsigned (N.v6571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6571 s i)) at 1.
  unfold R.v6571, N.v6571.
  rewrite ?node_6478.
  rewrite ?node_6481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6572 (s : N.State) (i : N.Inputs) :
  R.v6572 (state s) (inputs i) = Zmod.unsigned (N.v6572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6572 s i)) at 1.
  unfold R.v6572, N.v6572.
  rewrite ?node_6482.
  rewrite ?node_6485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6573 (s : N.State) (i : N.Inputs) :
  R.v6573 (state s) (inputs i) = Zmod.unsigned (N.v6573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6573 s i)) at 1.
  unfold R.v6573, N.v6573.
  rewrite ?node_6571.
  rewrite ?node_6572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6574 (s : N.State) (i : N.Inputs) :
  R.v6574 (state s) (inputs i) = Zmod.unsigned (N.v6574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6574 s i)) at 1.
  unfold R.v6574, N.v6574.
  rewrite ?node_6570.
  rewrite ?node_6573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6575 (s : N.State) (i : N.Inputs) :
  R.v6575 (state s) (inputs i) = Zmod.unsigned (N.v6575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6575 s i)) at 1.
  unfold R.v6575, N.v6575.
  rewrite ?node_6557.
  rewrite ?node_6574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6576 (s : N.State) (i : N.Inputs) :
  R.v6576 (state s) (inputs i) = Zmod.unsigned (N.v6576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6576 s i)) at 1.
  unfold R.v6576, N.v6576.
  rewrite ?node_6467.
  rewrite !state_r319_nr_5F319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r319_nr_5F319 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6577 (s : N.State) (i : N.Inputs) :
  R.v6577 (state s) (inputs i) = Zmod.unsigned (N.v6577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6577 s i)) at 1.
  unfold R.v6577, N.v6577.
  rewrite ?node_6468.
  rewrite ?node_6471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6578 (s : N.State) (i : N.Inputs) :
  R.v6578 (state s) (inputs i) = Zmod.unsigned (N.v6578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6578 s i)) at 1.
  unfold R.v6578, N.v6578.
  rewrite ?node_6576.
  rewrite ?node_6577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6579 (s : N.State) (i : N.Inputs) :
  R.v6579 (state s) (inputs i) = Zmod.unsigned (N.v6579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6579 s i)) at 1.
  unfold R.v6579, N.v6579.
  rewrite !state_r320_nr_5F320.
  rewrite !state_r321_nr_5F321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r320_nr_5F320 s)).
  rewrite ?(bits.mod_to_Z (N.r321_nr_5F321 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6580 (s : N.State) (i : N.Inputs) :
  R.v6580 (state s) (inputs i) = Zmod.unsigned (N.v6580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6580 s i)) at 1.
  unfold R.v6580, N.v6580.
  rewrite ?node_6578.
  rewrite ?node_6579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6581 (s : N.State) (i : N.Inputs) :
  R.v6581 (state s) (inputs i) = Zmod.unsigned (N.v6581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6581 s i)) at 1.
  unfold R.v6581, N.v6581.
  rewrite ?node_6575.
  rewrite ?node_6580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6582 (s : N.State) (i : N.Inputs) :
  R.v6582 (state s) (inputs i) = Zmod.unsigned (N.v6582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6582 s i)) at 1.
  unfold R.v6582, N.v6582.
  rewrite ?node_6465.
  rewrite ?node_6472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6583 (s : N.State) (i : N.Inputs) :
  R.v6583 (state s) (inputs i) = Zmod.unsigned (N.v6583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6583 s i)) at 1.
  unfold R.v6583, N.v6583.
  rewrite ?node_6473.
  rewrite ?node_6476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6584 (s : N.State) (i : N.Inputs) :
  R.v6584 (state s) (inputs i) = Zmod.unsigned (N.v6584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6584 s i)) at 1.
  unfold R.v6584, N.v6584.
  rewrite ?node_6582.
  rewrite ?node_6583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6585 (s : N.State) (i : N.Inputs) :
  R.v6585 (state s) (inputs i) = Zmod.unsigned (N.v6585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6585 s i)) at 1.
  unfold R.v6585, N.v6585.
  rewrite ?node_6581.
  rewrite ?node_6584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6586 (s : N.State) (i : N.Inputs) :
  R.v6586 (state s) (inputs i) = Zmod.unsigned (N.v6586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6586 s i)) at 1.
  unfold R.v6586, N.v6586.
  rewrite ?node_6477.
  rewrite ?node_6494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6587 (s : N.State) (i : N.Inputs) :
  R.v6587 (state s) (inputs i) = Zmod.unsigned (N.v6587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6587 s i)) at 1.
  unfold R.v6587, N.v6587.
  rewrite ?node_6495.
  rewrite ?node_6498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6588 (s : N.State) (i : N.Inputs) :
  R.v6588 (state s) (inputs i) = Zmod.unsigned (N.v6588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6588 s i)) at 1.
  unfold R.v6588, N.v6588.
  rewrite ?node_6586.
  rewrite ?node_6587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6589 (s : N.State) (i : N.Inputs) :
  R.v6589 (state s) (inputs i) = Zmod.unsigned (N.v6589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6589 s i)) at 1.
  unfold R.v6589, N.v6589.
  rewrite ?node_6585.
  rewrite ?node_6588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6590 (s : N.State) (i : N.Inputs) :
  R.v6590 (state s) (inputs i) = Zmod.unsigned (N.v6590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6590 s i)) at 1.
  unfold R.v6590, N.v6590.
  rewrite ?node_6486.
  rewrite ?node_6489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6591 (s : N.State) (i : N.Inputs) :
  R.v6591 (state s) (inputs i) = Zmod.unsigned (N.v6591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6591 s i)) at 1.
  unfold R.v6591, N.v6591.
  rewrite ?node_6490.
  rewrite ?node_6493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6592 (s : N.State) (i : N.Inputs) :
  R.v6592 (state s) (inputs i) = Zmod.unsigned (N.v6592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6592 s i)) at 1.
  unfold R.v6592, N.v6592.
  rewrite ?node_6590.
  rewrite ?node_6591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6593 (s : N.State) (i : N.Inputs) :
  R.v6593 (state s) (inputs i) = Zmod.unsigned (N.v6593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6593 s i)) at 1.
  unfold R.v6593, N.v6593.
  rewrite ?node_6589.
  rewrite ?node_6592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6594 (s : N.State) (i : N.Inputs) :
  R.v6594 (state s) (inputs i) = Zmod.unsigned (N.v6594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6594 s i)) at 1.
  unfold R.v6594, N.v6594.
  rewrite ?node_6499.
  rewrite ?node_6502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6595 (s : N.State) (i : N.Inputs) :
  R.v6595 (state s) (inputs i) = Zmod.unsigned (N.v6595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6595 s i)) at 1.
  unfold R.v6595, N.v6595.
  rewrite ?node_6503.
  rewrite ?node_6506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6596 (s : N.State) (i : N.Inputs) :
  R.v6596 (state s) (inputs i) = Zmod.unsigned (N.v6596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6596 s i)) at 1.
  unfold R.v6596, N.v6596.
  rewrite ?node_6594.
  rewrite ?node_6595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6597 (s : N.State) (i : N.Inputs) :
  R.v6597 (state s) (inputs i) = Zmod.unsigned (N.v6597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6597 s i)) at 1.
  unfold R.v6597, N.v6597.
  rewrite ?node_6593.
  rewrite ?node_6596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6598 (s : N.State) (i : N.Inputs) :
  R.v6598 (state s) (inputs i) = Zmod.unsigned (N.v6598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6598 s i)) at 1.
  unfold R.v6598, N.v6598.
  rewrite ?node_6507.
  rewrite ?node_6510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6599 (s : N.State) (i : N.Inputs) :
  R.v6599 (state s) (inputs i) = Zmod.unsigned (N.v6599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6599 s i)) at 1.
  unfold R.v6599, N.v6599.
  rewrite ?node_6511.
  rewrite ?node_6514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6600 (s : N.State) (i : N.Inputs) :
  R.v6600 (state s) (inputs i) = Zmod.unsigned (N.v6600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6600 s i)) at 1.
  unfold R.v6600, N.v6600.
  rewrite ?node_6598.
  rewrite ?node_6599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6601 (s : N.State) (i : N.Inputs) :
  R.v6601 (state s) (inputs i) = Zmod.unsigned (N.v6601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6601 s i)) at 1.
  unfold R.v6601, N.v6601.
  rewrite ?node_6597.
  rewrite ?node_6600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6602 (s : N.State) (i : N.Inputs) :
  R.v6602 (state s) (inputs i) = Zmod.unsigned (N.v6602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6602 s i)) at 1.
  unfold R.v6602, N.v6602.
  rewrite ?node_6601.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2339_nr_5F2370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2339_nr_5F2370 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6603 (s : N.State) (i : N.Inputs) :
  R.v6603 (state s) (inputs i) = Zmod.unsigned (N.v6603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6603 s i)) at 1.
  unfold R.v6603, N.v6603.
  rewrite ?node_6515.
  rewrite ?node_6518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6604 (s : N.State) (i : N.Inputs) :
  R.v6604 (state s) (inputs i) = Zmod.unsigned (N.v6604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6604 s i)) at 1.
  unfold R.v6604, N.v6604.
  rewrite ?node_6603.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2340_nr_5F2371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2340_nr_5F2371 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6605 (s : N.State) (i : N.Inputs) :
  R.v6605 (state s) (inputs i) = Zmod.unsigned (N.v6605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6605 s i)) at 1.
  unfold R.v6605, N.v6605.
  rewrite !state_r340_nr_5F340.
  rewrite !state_r341_nr_5F341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r340_nr_5F340 s)).
  rewrite ?(bits.mod_to_Z (N.r341_nr_5F341 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6606 (s : N.State) (i : N.Inputs) :
  R.v6606 (state s) (inputs i) = Zmod.unsigned (N.v6606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6606 s i)) at 1.
  unfold R.v6606, N.v6606.
  rewrite ?node_6605.
  rewrite !state_r342_nr_5F342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r342_nr_5F342 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6607 (s : N.State) (i : N.Inputs) :
  R.v6607 (state s) (inputs i) = Zmod.unsigned (N.v6607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6607 s i)) at 1.
  unfold R.v6607, N.v6607.
  rewrite ?node_6606.
  rewrite !state_r343_nr_5F343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r343_nr_5F343 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6608 (s : N.State) (i : N.Inputs) :
  R.v6608 (state s) (inputs i) = Zmod.unsigned (N.v6608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6608 s i)) at 1.
  unfold R.v6608, N.v6608.
  rewrite !state_r322_nr_5F322.
  rewrite !state_r323_nr_5F323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r322_nr_5F322 s)).
  rewrite ?(bits.mod_to_Z (N.r323_nr_5F323 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6609 (s : N.State) (i : N.Inputs) :
  R.v6609 (state s) (inputs i) = Zmod.unsigned (N.v6609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6609 s i)) at 1.
  unfold R.v6609, N.v6609.
  rewrite ?node_6523.
  rewrite !state_r324_nr_5F324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r324_nr_5F324 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6610 (s : N.State) (i : N.Inputs) :
  R.v6610 (state s) (inputs i) = Zmod.unsigned (N.v6610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6610 s i)) at 1.
  unfold R.v6610, N.v6610.
  rewrite ?node_6608.
  rewrite ?node_6609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6611 (s : N.State) (i : N.Inputs) :
  R.v6611 (state s) (inputs i) = Zmod.unsigned (N.v6611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6611 s i)) at 1.
  unfold R.v6611, N.v6611.
  rewrite ?node_6607.
  rewrite ?node_6610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6612 (s : N.State) (i : N.Inputs) :
  R.v6612 (state s) (inputs i) = Zmod.unsigned (N.v6612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6612 s i)) at 1.
  unfold R.v6612, N.v6612.
  rewrite !state_r344_nr_5F344.
  rewrite !state_r345_nr_5F345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r344_nr_5F344 s)).
  rewrite ?(bits.mod_to_Z (N.r345_nr_5F345 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6613 (s : N.State) (i : N.Inputs) :
  R.v6613 (state s) (inputs i) = Zmod.unsigned (N.v6613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6613 s i)) at 1.
  unfold R.v6613, N.v6613.
  rewrite ?node_6612.
  rewrite !state_r346_nr_5F346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r346_nr_5F346 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6614 (s : N.State) (i : N.Inputs) :
  R.v6614 (state s) (inputs i) = Zmod.unsigned (N.v6614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6614 s i)) at 1.
  unfold R.v6614, N.v6614.
  rewrite ?node_6613.
  rewrite !state_r347_nr_5F347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r347_nr_5F347 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6615 (s : N.State) (i : N.Inputs) :
  R.v6615 (state s) (inputs i) = Zmod.unsigned (N.v6615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6615 s i)) at 1.
  unfold R.v6615, N.v6615.
  rewrite !state_r326_nr_5F326.
  rewrite !state_r327_nr_5F327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r326_nr_5F326 s)).
  rewrite ?(bits.mod_to_Z (N.r327_nr_5F327 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6616 (s : N.State) (i : N.Inputs) :
  R.v6616 (state s) (inputs i) = Zmod.unsigned (N.v6616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6616 s i)) at 1.
  unfold R.v6616, N.v6616.
  rewrite ?node_6530.
  rewrite !state_r328_nr_5F328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r328_nr_5F328 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6617 (s : N.State) (i : N.Inputs) :
  R.v6617 (state s) (inputs i) = Zmod.unsigned (N.v6617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6617 s i)) at 1.
  unfold R.v6617, N.v6617.
  rewrite ?node_6615.
  rewrite ?node_6616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6618 (s : N.State) (i : N.Inputs) :
  R.v6618 (state s) (inputs i) = Zmod.unsigned (N.v6618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6618 s i)) at 1.
  unfold R.v6618, N.v6618.
  rewrite ?node_6614.
  rewrite ?node_6617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6619 (s : N.State) (i : N.Inputs) :
  R.v6619 (state s) (inputs i) = Zmod.unsigned (N.v6619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6619 s i)) at 1.
  unfold R.v6619, N.v6619.
  rewrite ?node_6611.
  rewrite ?node_6618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6620 (s : N.State) (i : N.Inputs) :
  R.v6620 (state s) (inputs i) = Zmod.unsigned (N.v6620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6620 s i)) at 1.
  unfold R.v6620, N.v6620.
  rewrite !state_r348_nr_5F348.
  rewrite !state_r349_nr_5F349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r348_nr_5F348 s)).
  rewrite ?(bits.mod_to_Z (N.r349_nr_5F349 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6621 (s : N.State) (i : N.Inputs) :
  R.v6621 (state s) (inputs i) = Zmod.unsigned (N.v6621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6621 s i)) at 1.
  unfold R.v6621, N.v6621.
  rewrite ?node_6620.
  rewrite !state_r350_nr_5F350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r350_nr_5F350 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6622 (s : N.State) (i : N.Inputs) :
  R.v6622 (state s) (inputs i) = Zmod.unsigned (N.v6622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6622 s i)) at 1.
  unfold R.v6622, N.v6622.
  rewrite ?node_6621.
  rewrite !state_r351_nr_5F351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r351_nr_5F351 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6623 (s : N.State) (i : N.Inputs) :
  R.v6623 (state s) (inputs i) = Zmod.unsigned (N.v6623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6623 s i)) at 1.
  unfold R.v6623, N.v6623.
  rewrite !state_r330_nr_5F330.
  rewrite !state_r331_nr_5F331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r330_nr_5F330 s)).
  rewrite ?(bits.mod_to_Z (N.r331_nr_5F331 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6624 (s : N.State) (i : N.Inputs) :
  R.v6624 (state s) (inputs i) = Zmod.unsigned (N.v6624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6624 s i)) at 1.
  unfold R.v6624, N.v6624.
  rewrite ?node_6538.
  rewrite !state_r332_nr_5F332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r332_nr_5F332 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6625 (s : N.State) (i : N.Inputs) :
  R.v6625 (state s) (inputs i) = Zmod.unsigned (N.v6625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6625 s i)) at 1.
  unfold R.v6625, N.v6625.
  rewrite ?node_6623.
  rewrite ?node_6624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6626 (s : N.State) (i : N.Inputs) :
  R.v6626 (state s) (inputs i) = Zmod.unsigned (N.v6626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6626 s i)) at 1.
  unfold R.v6626, N.v6626.
  rewrite ?node_6622.
  rewrite ?node_6625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6627 (s : N.State) (i : N.Inputs) :
  R.v6627 (state s) (inputs i) = Zmod.unsigned (N.v6627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6627 s i)) at 1.
  unfold R.v6627, N.v6627.
  rewrite ?node_6619.
  rewrite ?node_6626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6628 (s : N.State) (i : N.Inputs) :
  R.v6628 (state s) (inputs i) = Zmod.unsigned (N.v6628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6628 s i)) at 1.
  unfold R.v6628, N.v6628.
  rewrite !state_r352_nr_5F352.
  rewrite !state_r353_nr_5F353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r352_nr_5F352 s)).
  rewrite ?(bits.mod_to_Z (N.r353_nr_5F353 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6629 (s : N.State) (i : N.Inputs) :
  R.v6629 (state s) (inputs i) = Zmod.unsigned (N.v6629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6629 s i)) at 1.
  unfold R.v6629, N.v6629.
  rewrite ?node_6628.
  rewrite !state_r354_nr_5F354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r354_nr_5F354 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6630 (s : N.State) (i : N.Inputs) :
  R.v6630 (state s) (inputs i) = Zmod.unsigned (N.v6630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6630 s i)) at 1.
  unfold R.v6630, N.v6630.
  rewrite ?node_6629.
  rewrite !state_r355_nr_5F355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r355_nr_5F355 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6631 (s : N.State) (i : N.Inputs) :
  R.v6631 (state s) (inputs i) = Zmod.unsigned (N.v6631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6631 s i)) at 1.
  unfold R.v6631, N.v6631.
  rewrite !state_r334_nr_5F334.
  rewrite !state_r335_nr_5F335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r334_nr_5F334 s)).
  rewrite ?(bits.mod_to_Z (N.r335_nr_5F335 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6632 (s : N.State) (i : N.Inputs) :
  R.v6632 (state s) (inputs i) = Zmod.unsigned (N.v6632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6632 s i)) at 1.
  unfold R.v6632, N.v6632.
  rewrite ?node_6546.
  rewrite !state_r336_nr_5F336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r336_nr_5F336 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6633 (s : N.State) (i : N.Inputs) :
  R.v6633 (state s) (inputs i) = Zmod.unsigned (N.v6633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6633 s i)) at 1.
  unfold R.v6633, N.v6633.
  rewrite ?node_6631.
  rewrite ?node_6632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6634 (s : N.State) (i : N.Inputs) :
  R.v6634 (state s) (inputs i) = Zmod.unsigned (N.v6634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6634 s i)) at 1.
  unfold R.v6634, N.v6634.
  rewrite ?node_6630.
  rewrite ?node_6633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6635 (s : N.State) (i : N.Inputs) :
  R.v6635 (state s) (inputs i) = Zmod.unsigned (N.v6635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6635 s i)) at 1.
  unfold R.v6635, N.v6635.
  rewrite ?node_6627.
  rewrite ?node_6634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6636 (s : N.State) (i : N.Inputs) :
  R.v6636 (state s) (inputs i) = Zmod.unsigned (N.v6636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6636 s i)) at 1.
  unfold R.v6636, N.v6636.
  rewrite ?node_6529.
  rewrite ?node_6536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6637 (s : N.State) (i : N.Inputs) :
  R.v6637 (state s) (inputs i) = Zmod.unsigned (N.v6637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6637 s i)) at 1.
  unfold R.v6637, N.v6637.
  rewrite ?node_6537.
  rewrite ?node_6544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6638 (s : N.State) (i : N.Inputs) :
  R.v6638 (state s) (inputs i) = Zmod.unsigned (N.v6638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6638 s i)) at 1.
  unfold R.v6638, N.v6638.
  rewrite ?node_6636.
  rewrite ?node_6637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6639 (s : N.State) (i : N.Inputs) :
  R.v6639 (state s) (inputs i) = Zmod.unsigned (N.v6639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6639 s i)) at 1.
  unfold R.v6639, N.v6639.
  rewrite ?node_6635.
  rewrite ?node_6638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6640 (s : N.State) (i : N.Inputs) :
  R.v6640 (state s) (inputs i) = Zmod.unsigned (N.v6640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6640 s i)) at 1.
  unfold R.v6640, N.v6640.
  rewrite !state_r356_nr_5F356.
  rewrite !state_r357_nr_5F357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r356_nr_5F356 s)).
  rewrite ?(bits.mod_to_Z (N.r357_nr_5F357 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6641 (s : N.State) (i : N.Inputs) :
  R.v6641 (state s) (inputs i) = Zmod.unsigned (N.v6641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6641 s i)) at 1.
  unfold R.v6641, N.v6641.
  rewrite ?node_6640.
  rewrite !state_r358_nr_5F358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r358_nr_5F358 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6642 (s : N.State) (i : N.Inputs) :
  R.v6642 (state s) (inputs i) = Zmod.unsigned (N.v6642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6642 s i)) at 1.
  unfold R.v6642, N.v6642.
  rewrite ?node_6524.
  rewrite !state_r325_nr_5F325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r325_nr_5F325 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6643 (s : N.State) (i : N.Inputs) :
  R.v6643 (state s) (inputs i) = Zmod.unsigned (N.v6643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6643 s i)) at 1.
  unfold R.v6643, N.v6643.
  rewrite ?node_6525.
  rewrite ?node_6528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6644 (s : N.State) (i : N.Inputs) :
  R.v6644 (state s) (inputs i) = Zmod.unsigned (N.v6644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6644 s i)) at 1.
  unfold R.v6644, N.v6644.
  rewrite ?node_6642.
  rewrite ?node_6643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6645 (s : N.State) (i : N.Inputs) :
  R.v6645 (state s) (inputs i) = Zmod.unsigned (N.v6645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6645 s i)) at 1.
  unfold R.v6645, N.v6645.
  rewrite ?node_6641.
  rewrite ?node_6644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6646 (s : N.State) (i : N.Inputs) :
  R.v6646 (state s) (inputs i) = Zmod.unsigned (N.v6646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6646 s i)) at 1.
  unfold R.v6646, N.v6646.
  rewrite ?node_6531.
  rewrite !state_r329_nr_5F329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r329_nr_5F329 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6647 (s : N.State) (i : N.Inputs) :
  R.v6647 (state s) (inputs i) = Zmod.unsigned (N.v6647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6647 s i)) at 1.
  unfold R.v6647, N.v6647.
  rewrite ?node_6532.
  rewrite ?node_6535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6648 (s : N.State) (i : N.Inputs) :
  R.v6648 (state s) (inputs i) = Zmod.unsigned (N.v6648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6648 s i)) at 1.
  unfold R.v6648, N.v6648.
  rewrite ?node_6646.
  rewrite ?node_6647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6649 (s : N.State) (i : N.Inputs) :
  R.v6649 (state s) (inputs i) = Zmod.unsigned (N.v6649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6649 s i)) at 1.
  unfold R.v6649, N.v6649.
  rewrite ?node_6645.
  rewrite ?node_6648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6650 (s : N.State) (i : N.Inputs) :
  R.v6650 (state s) (inputs i) = Zmod.unsigned (N.v6650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6650 s i)) at 1.
  unfold R.v6650, N.v6650.
  rewrite ?node_6539.
  rewrite !state_r333_nr_5F333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r333_nr_5F333 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6651 (s : N.State) (i : N.Inputs) :
  R.v6651 (state s) (inputs i) = Zmod.unsigned (N.v6651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6651 s i)) at 1.
  unfold R.v6651, N.v6651.
  rewrite ?node_6540.
  rewrite ?node_6543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6652 (s : N.State) (i : N.Inputs) :
  R.v6652 (state s) (inputs i) = Zmod.unsigned (N.v6652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6652 s i)) at 1.
  unfold R.v6652, N.v6652.
  rewrite ?node_6650.
  rewrite ?node_6651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6653 (s : N.State) (i : N.Inputs) :
  R.v6653 (state s) (inputs i) = Zmod.unsigned (N.v6653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6653 s i)) at 1.
  unfold R.v6653, N.v6653.
  rewrite ?node_6649.
  rewrite ?node_6652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6654 (s : N.State) (i : N.Inputs) :
  R.v6654 (state s) (inputs i) = Zmod.unsigned (N.v6654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6654 s i)) at 1.
  unfold R.v6654, N.v6654.
  rewrite ?node_6558.
  rewrite ?node_6561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6655 (s : N.State) (i : N.Inputs) :
  R.v6655 (state s) (inputs i) = Zmod.unsigned (N.v6655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6655 s i)) at 1.
  unfold R.v6655, N.v6655.
  rewrite ?node_6562.
  rewrite ?node_6565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6656 (s : N.State) (i : N.Inputs) :
  R.v6656 (state s) (inputs i) = Zmod.unsigned (N.v6656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6656 s i)) at 1.
  unfold R.v6656, N.v6656.
  rewrite ?node_6654.
  rewrite ?node_6655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6657 (s : N.State) (i : N.Inputs) :
  R.v6657 (state s) (inputs i) = Zmod.unsigned (N.v6657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6657 s i)) at 1.
  unfold R.v6657, N.v6657.
  rewrite ?node_6653.
  rewrite ?node_6656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6658 (s : N.State) (i : N.Inputs) :
  R.v6658 (state s) (inputs i) = Zmod.unsigned (N.v6658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6658 s i)) at 1.
  unfold R.v6658, N.v6658.
  rewrite ?node_6639.
  rewrite ?node_6657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6659 (s : N.State) (i : N.Inputs) :
  R.v6659 (state s) (inputs i) = Zmod.unsigned (N.v6659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6659 s i)) at 1.
  unfold R.v6659, N.v6659.
  rewrite ?node_6547.
  rewrite !state_r337_nr_5F337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r337_nr_5F337 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6660 (s : N.State) (i : N.Inputs) :
  R.v6660 (state s) (inputs i) = Zmod.unsigned (N.v6660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6660 s i)) at 1.
  unfold R.v6660, N.v6660.
  rewrite ?node_6548.
  rewrite ?node_6551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6661 (s : N.State) (i : N.Inputs) :
  R.v6661 (state s) (inputs i) = Zmod.unsigned (N.v6661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6661 s i)) at 1.
  unfold R.v6661, N.v6661.
  rewrite ?node_6659.
  rewrite ?node_6660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6662 (s : N.State) (i : N.Inputs) :
  R.v6662 (state s) (inputs i) = Zmod.unsigned (N.v6662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6662 s i)) at 1.
  unfold R.v6662, N.v6662.
  rewrite !state_r338_nr_5F338.
  rewrite !state_r339_nr_5F339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r338_nr_5F338 s)).
  rewrite ?(bits.mod_to_Z (N.r339_nr_5F339 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6663 (s : N.State) (i : N.Inputs) :
  R.v6663 (state s) (inputs i) = Zmod.unsigned (N.v6663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6663 s i)) at 1.
  unfold R.v6663, N.v6663.
  rewrite ?node_6661.
  rewrite ?node_6662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6664 (s : N.State) (i : N.Inputs) :
  R.v6664 (state s) (inputs i) = Zmod.unsigned (N.v6664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6664 s i)) at 1.
  unfold R.v6664, N.v6664.
  rewrite ?node_6658.
  rewrite ?node_6663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6665 (s : N.State) (i : N.Inputs) :
  R.v6665 (state s) (inputs i) = Zmod.unsigned (N.v6665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6665 s i)) at 1.
  unfold R.v6665, N.v6665.
  rewrite ?node_6545.
  rewrite ?node_6552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6666 (s : N.State) (i : N.Inputs) :
  R.v6666 (state s) (inputs i) = Zmod.unsigned (N.v6666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6666 s i)) at 1.
  unfold R.v6666, N.v6666.
  rewrite ?node_6553.
  rewrite ?node_6556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6667 (s : N.State) (i : N.Inputs) :
  R.v6667 (state s) (inputs i) = Zmod.unsigned (N.v6667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6667 s i)) at 1.
  unfold R.v6667, N.v6667.
  rewrite ?node_6665.
  rewrite ?node_6666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6668 (s : N.State) (i : N.Inputs) :
  R.v6668 (state s) (inputs i) = Zmod.unsigned (N.v6668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6668 s i)) at 1.
  unfold R.v6668, N.v6668.
  rewrite ?node_6664.
  rewrite ?node_6667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6669 (s : N.State) (i : N.Inputs) :
  R.v6669 (state s) (inputs i) = Zmod.unsigned (N.v6669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6669 s i)) at 1.
  unfold R.v6669, N.v6669.
  rewrite ?node_6557.
  rewrite ?node_6574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6670 (s : N.State) (i : N.Inputs) :
  R.v6670 (state s) (inputs i) = Zmod.unsigned (N.v6670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6670 s i)) at 1.
  unfold R.v6670, N.v6670.
  rewrite ?node_6575.
  rewrite ?node_6580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6671 (s : N.State) (i : N.Inputs) :
  R.v6671 (state s) (inputs i) = Zmod.unsigned (N.v6671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6671 s i)) at 1.
  unfold R.v6671, N.v6671.
  rewrite ?node_6669.
  rewrite ?node_6670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6672 (s : N.State) (i : N.Inputs) :
  R.v6672 (state s) (inputs i) = Zmod.unsigned (N.v6672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6672 s i)) at 1.
  unfold R.v6672, N.v6672.
  rewrite ?node_6668.
  rewrite ?node_6671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6673 (s : N.State) (i : N.Inputs) :
  R.v6673 (state s) (inputs i) = Zmod.unsigned (N.v6673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6673 s i)) at 1.
  unfold R.v6673, N.v6673.
  rewrite ?node_6566.
  rewrite ?node_6569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6674 (s : N.State) (i : N.Inputs) :
  R.v6674 (state s) (inputs i) = Zmod.unsigned (N.v6674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6674 s i)) at 1.
  unfold R.v6674, N.v6674.
  rewrite ?node_6570.
  rewrite ?node_6573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6675 (s : N.State) (i : N.Inputs) :
  R.v6675 (state s) (inputs i) = Zmod.unsigned (N.v6675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6675 s i)) at 1.
  unfold R.v6675, N.v6675.
  rewrite ?node_6673.
  rewrite ?node_6674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6676 (s : N.State) (i : N.Inputs) :
  R.v6676 (state s) (inputs i) = Zmod.unsigned (N.v6676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6676 s i)) at 1.
  unfold R.v6676, N.v6676.
  rewrite ?node_6578.
  rewrite ?node_6579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6677 (s : N.State) (i : N.Inputs) :
  R.v6677 (state s) (inputs i) = Zmod.unsigned (N.v6677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6677 s i)) at 1.
  unfold R.v6677, N.v6677.
  rewrite ?node_6675.
  rewrite ?node_6676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6678 (s : N.State) (i : N.Inputs) :
  R.v6678 (state s) (inputs i) = Zmod.unsigned (N.v6678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6678 s i)) at 1.
  unfold R.v6678, N.v6678.
  rewrite ?node_6672.
  rewrite ?node_6677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6679 (s : N.State) (i : N.Inputs) :
  R.v6679 (state s) (inputs i) = Zmod.unsigned (N.v6679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6679 s i)) at 1.
  unfold R.v6679, N.v6679.
  rewrite ?node_6581.
  rewrite ?node_6584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6680 (s : N.State) (i : N.Inputs) :
  R.v6680 (state s) (inputs i) = Zmod.unsigned (N.v6680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6680 s i)) at 1.
  unfold R.v6680, N.v6680.
  rewrite ?node_6585.
  rewrite ?node_6588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6681 (s : N.State) (i : N.Inputs) :
  R.v6681 (state s) (inputs i) = Zmod.unsigned (N.v6681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6681 s i)) at 1.
  unfold R.v6681, N.v6681.
  rewrite ?node_6679.
  rewrite ?node_6680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6682 (s : N.State) (i : N.Inputs) :
  R.v6682 (state s) (inputs i) = Zmod.unsigned (N.v6682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6682 s i)) at 1.
  unfold R.v6682, N.v6682.
  rewrite ?node_6678.
  rewrite ?node_6681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6683 (s : N.State) (i : N.Inputs) :
  R.v6683 (state s) (inputs i) = Zmod.unsigned (N.v6683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6683 s i)) at 1.
  unfold R.v6683, N.v6683.
  rewrite ?node_6589.
  rewrite ?node_6592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6684 (s : N.State) (i : N.Inputs) :
  R.v6684 (state s) (inputs i) = Zmod.unsigned (N.v6684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6684 s i)) at 1.
  unfold R.v6684, N.v6684.
  rewrite ?node_6593.
  rewrite ?node_6596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6685 (s : N.State) (i : N.Inputs) :
  R.v6685 (state s) (inputs i) = Zmod.unsigned (N.v6685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6685 s i)) at 1.
  unfold R.v6685, N.v6685.
  rewrite ?node_6683.
  rewrite ?node_6684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6686 (s : N.State) (i : N.Inputs) :
  R.v6686 (state s) (inputs i) = Zmod.unsigned (N.v6686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6686 s i)) at 1.
  unfold R.v6686, N.v6686.
  rewrite ?node_6682.
  rewrite ?node_6685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6687 (s : N.State) (i : N.Inputs) :
  R.v6687 (state s) (inputs i) = Zmod.unsigned (N.v6687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6687 s i)) at 1.
  unfold R.v6687, N.v6687.
  rewrite ?node_6686.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2341_nr_5F2372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2341_nr_5F2372 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6688 (s : N.State) (i : N.Inputs) :
  R.v6688 (state s) (inputs i) = Zmod.unsigned (N.v6688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6688 s i)) at 1.
  unfold R.v6688, N.v6688.
  rewrite ?node_6597.
  rewrite ?node_6600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6689 (s : N.State) (i : N.Inputs) :
  R.v6689 (state s) (inputs i) = Zmod.unsigned (N.v6689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6689 s i)) at 1.
  unfold R.v6689, N.v6689.
  rewrite ?node_6688.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2342_nr_5F2373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2342_nr_5F2373 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6690 (s : N.State) (i : N.Inputs) :
  R.v6690 (state s) (inputs i) = Zmod.unsigned (N.v6690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6690 s i)) at 1.
  unfold R.v6690, N.v6690.
  rewrite !state_r359_nr_5F359.
  rewrite !state_r360_nr_5F360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r359_nr_5F359 s)).
  rewrite ?(bits.mod_to_Z (N.r360_nr_5F360 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6691 (s : N.State) (i : N.Inputs) :
  R.v6691 (state s) (inputs i) = Zmod.unsigned (N.v6691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6691 s i)) at 1.
  unfold R.v6691, N.v6691.
  rewrite ?node_6690.
  rewrite !state_r361_nr_5F361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r361_nr_5F361 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6692 (s : N.State) (i : N.Inputs) :
  R.v6692 (state s) (inputs i) = Zmod.unsigned (N.v6692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6692 s i)) at 1.
  unfold R.v6692, N.v6692.
  rewrite ?node_6691.
  rewrite !state_r362_nr_5F362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r362_nr_5F362 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6693 (s : N.State) (i : N.Inputs) :
  R.v6693 (state s) (inputs i) = Zmod.unsigned (N.v6693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6693 s i)) at 1.
  unfold R.v6693, N.v6693.
  rewrite !state_r340_nr_5F340.
  rewrite !state_r341_nr_5F341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r340_nr_5F340 s)).
  rewrite ?(bits.mod_to_Z (N.r341_nr_5F341 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6694 (s : N.State) (i : N.Inputs) :
  R.v6694 (state s) (inputs i) = Zmod.unsigned (N.v6694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6694 s i)) at 1.
  unfold R.v6694, N.v6694.
  rewrite ?node_6605.
  rewrite !state_r342_nr_5F342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r342_nr_5F342 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6695 (s : N.State) (i : N.Inputs) :
  R.v6695 (state s) (inputs i) = Zmod.unsigned (N.v6695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6695 s i)) at 1.
  unfold R.v6695, N.v6695.
  rewrite ?node_6693.
  rewrite ?node_6694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6696 (s : N.State) (i : N.Inputs) :
  R.v6696 (state s) (inputs i) = Zmod.unsigned (N.v6696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6696 s i)) at 1.
  unfold R.v6696, N.v6696.
  rewrite ?node_6692.
  rewrite ?node_6695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6697 (s : N.State) (i : N.Inputs) :
  R.v6697 (state s) (inputs i) = Zmod.unsigned (N.v6697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6697 s i)) at 1.
  unfold R.v6697, N.v6697.
  rewrite !state_r363_nr_5F363.
  rewrite !state_r364_nr_5F364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r363_nr_5F363 s)).
  rewrite ?(bits.mod_to_Z (N.r364_nr_5F364 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6698 (s : N.State) (i : N.Inputs) :
  R.v6698 (state s) (inputs i) = Zmod.unsigned (N.v6698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6698 s i)) at 1.
  unfold R.v6698, N.v6698.
  rewrite ?node_6697.
  rewrite !state_r365_nr_5F365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r365_nr_5F365 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6699 (s : N.State) (i : N.Inputs) :
  R.v6699 (state s) (inputs i) = Zmod.unsigned (N.v6699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6699 s i)) at 1.
  unfold R.v6699, N.v6699.
  rewrite ?node_6698.
  rewrite !state_r366_nr_5F366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r366_nr_5F366 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6700 (s : N.State) (i : N.Inputs) :
  R.v6700 (state s) (inputs i) = Zmod.unsigned (N.v6700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6700 s i)) at 1.
  unfold R.v6700, N.v6700.
  rewrite !state_r344_nr_5F344.
  rewrite !state_r345_nr_5F345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r344_nr_5F344 s)).
  rewrite ?(bits.mod_to_Z (N.r345_nr_5F345 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6701 (s : N.State) (i : N.Inputs) :
  R.v6701 (state s) (inputs i) = Zmod.unsigned (N.v6701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6701 s i)) at 1.
  unfold R.v6701, N.v6701.
  rewrite ?node_6612.
  rewrite !state_r346_nr_5F346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r346_nr_5F346 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6702 (s : N.State) (i : N.Inputs) :
  R.v6702 (state s) (inputs i) = Zmod.unsigned (N.v6702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6702 s i)) at 1.
  unfold R.v6702, N.v6702.
  rewrite ?node_6700.
  rewrite ?node_6701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6703 (s : N.State) (i : N.Inputs) :
  R.v6703 (state s) (inputs i) = Zmod.unsigned (N.v6703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6703 s i)) at 1.
  unfold R.v6703, N.v6703.
  rewrite ?node_6699.
  rewrite ?node_6702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6704 (s : N.State) (i : N.Inputs) :
  R.v6704 (state s) (inputs i) = Zmod.unsigned (N.v6704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6704 s i)) at 1.
  unfold R.v6704, N.v6704.
  rewrite ?node_6696.
  rewrite ?node_6703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6705 (s : N.State) (i : N.Inputs) :
  R.v6705 (state s) (inputs i) = Zmod.unsigned (N.v6705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6705 s i)) at 1.
  unfold R.v6705, N.v6705.
  rewrite !state_r367_nr_5F367.
  rewrite !state_r368_nr_5F368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r367_nr_5F367 s)).
  rewrite ?(bits.mod_to_Z (N.r368_nr_5F368 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6706 (s : N.State) (i : N.Inputs) :
  R.v6706 (state s) (inputs i) = Zmod.unsigned (N.v6706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6706 s i)) at 1.
  unfold R.v6706, N.v6706.
  rewrite ?node_6705.
  rewrite !state_r369_nr_5F369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r369_nr_5F369 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6707 (s : N.State) (i : N.Inputs) :
  R.v6707 (state s) (inputs i) = Zmod.unsigned (N.v6707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6707 s i)) at 1.
  unfold R.v6707, N.v6707.
  rewrite ?node_6706.
  rewrite !state_r370_nr_5F370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r370_nr_5F370 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6708 (s : N.State) (i : N.Inputs) :
  R.v6708 (state s) (inputs i) = Zmod.unsigned (N.v6708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6708 s i)) at 1.
  unfold R.v6708, N.v6708.
  rewrite !state_r348_nr_5F348.
  rewrite !state_r349_nr_5F349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r348_nr_5F348 s)).
  rewrite ?(bits.mod_to_Z (N.r349_nr_5F349 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6709 (s : N.State) (i : N.Inputs) :
  R.v6709 (state s) (inputs i) = Zmod.unsigned (N.v6709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6709 s i)) at 1.
  unfold R.v6709, N.v6709.
  rewrite ?node_6620.
  rewrite !state_r350_nr_5F350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r350_nr_5F350 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6710 (s : N.State) (i : N.Inputs) :
  R.v6710 (state s) (inputs i) = Zmod.unsigned (N.v6710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6710 s i)) at 1.
  unfold R.v6710, N.v6710.
  rewrite ?node_6708.
  rewrite ?node_6709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6711 (s : N.State) (i : N.Inputs) :
  R.v6711 (state s) (inputs i) = Zmod.unsigned (N.v6711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6711 s i)) at 1.
  unfold R.v6711, N.v6711.
  rewrite ?node_6707.
  rewrite ?node_6710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6712 (s : N.State) (i : N.Inputs) :
  R.v6712 (state s) (inputs i) = Zmod.unsigned (N.v6712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6712 s i)) at 1.
  unfold R.v6712, N.v6712.
  rewrite ?node_6704.
  rewrite ?node_6711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6713 (s : N.State) (i : N.Inputs) :
  R.v6713 (state s) (inputs i) = Zmod.unsigned (N.v6713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6713 s i)) at 1.
  unfold R.v6713, N.v6713.
  rewrite !state_r371_nr_5F371.
  rewrite !state_r372_nr_5F372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r371_nr_5F371 s)).
  rewrite ?(bits.mod_to_Z (N.r372_nr_5F372 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6714 (s : N.State) (i : N.Inputs) :
  R.v6714 (state s) (inputs i) = Zmod.unsigned (N.v6714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6714 s i)) at 1.
  unfold R.v6714, N.v6714.
  rewrite ?node_6713.
  rewrite !state_r373_nr_5F373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r373_nr_5F373 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6715 (s : N.State) (i : N.Inputs) :
  R.v6715 (state s) (inputs i) = Zmod.unsigned (N.v6715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6715 s i)) at 1.
  unfold R.v6715, N.v6715.
  rewrite ?node_6714.
  rewrite !state_r374_nr_5F374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r374_nr_5F374 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6716 (s : N.State) (i : N.Inputs) :
  R.v6716 (state s) (inputs i) = Zmod.unsigned (N.v6716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6716 s i)) at 1.
  unfold R.v6716, N.v6716.
  rewrite !state_r352_nr_5F352.
  rewrite !state_r353_nr_5F353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r352_nr_5F352 s)).
  rewrite ?(bits.mod_to_Z (N.r353_nr_5F353 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6717 (s : N.State) (i : N.Inputs) :
  R.v6717 (state s) (inputs i) = Zmod.unsigned (N.v6717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6717 s i)) at 1.
  unfold R.v6717, N.v6717.
  rewrite ?node_6628.
  rewrite !state_r354_nr_5F354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r354_nr_5F354 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6718 (s : N.State) (i : N.Inputs) :
  R.v6718 (state s) (inputs i) = Zmod.unsigned (N.v6718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6718 s i)) at 1.
  unfold R.v6718, N.v6718.
  rewrite ?node_6716.
  rewrite ?node_6717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6719 (s : N.State) (i : N.Inputs) :
  R.v6719 (state s) (inputs i) = Zmod.unsigned (N.v6719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6719 s i)) at 1.
  unfold R.v6719, N.v6719.
  rewrite ?node_6715.
  rewrite ?node_6718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6720 (s : N.State) (i : N.Inputs) :
  R.v6720 (state s) (inputs i) = Zmod.unsigned (N.v6720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6720 s i)) at 1.
  unfold R.v6720, N.v6720.
  rewrite ?node_6712.
  rewrite ?node_6719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6721 (s : N.State) (i : N.Inputs) :
  R.v6721 (state s) (inputs i) = Zmod.unsigned (N.v6721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6721 s i)) at 1.
  unfold R.v6721, N.v6721.
  rewrite ?node_6611.
  rewrite ?node_6618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6722 (s : N.State) (i : N.Inputs) :
  R.v6722 (state s) (inputs i) = Zmod.unsigned (N.v6722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6722 s i)) at 1.
  unfold R.v6722, N.v6722.
  rewrite ?node_6619.
  rewrite ?node_6626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6723 (s : N.State) (i : N.Inputs) :
  R.v6723 (state s) (inputs i) = Zmod.unsigned (N.v6723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6723 s i)) at 1.
  unfold R.v6723, N.v6723.
  rewrite ?node_6721.
  rewrite ?node_6722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6724 (s : N.State) (i : N.Inputs) :
  R.v6724 (state s) (inputs i) = Zmod.unsigned (N.v6724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6724 s i)) at 1.
  unfold R.v6724, N.v6724.
  rewrite ?node_6720.
  rewrite ?node_6723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6725 (s : N.State) (i : N.Inputs) :
  R.v6725 (state s) (inputs i) = Zmod.unsigned (N.v6725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6725 s i)) at 1.
  unfold R.v6725, N.v6725.
  rewrite !state_r375_nr_5F375.
  rewrite !state_r376_nr_5F376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r375_nr_5F375 s)).
  rewrite ?(bits.mod_to_Z (N.r376_nr_5F376 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6726 (s : N.State) (i : N.Inputs) :
  R.v6726 (state s) (inputs i) = Zmod.unsigned (N.v6726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6726 s i)) at 1.
  unfold R.v6726, N.v6726.
  rewrite ?node_6725.
  rewrite !state_r377_nr_5F377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r377_nr_5F377 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6727 (s : N.State) (i : N.Inputs) :
  R.v6727 (state s) (inputs i) = Zmod.unsigned (N.v6727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6727 s i)) at 1.
  unfold R.v6727, N.v6727.
  rewrite ?node_6606.
  rewrite !state_r343_nr_5F343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r343_nr_5F343 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6728 (s : N.State) (i : N.Inputs) :
  R.v6728 (state s) (inputs i) = Zmod.unsigned (N.v6728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6728 s i)) at 1.
  unfold R.v6728, N.v6728.
  rewrite ?node_6607.
  rewrite ?node_6610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6729 (s : N.State) (i : N.Inputs) :
  R.v6729 (state s) (inputs i) = Zmod.unsigned (N.v6729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6729 s i)) at 1.
  unfold R.v6729, N.v6729.
  rewrite ?node_6727.
  rewrite ?node_6728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6730 (s : N.State) (i : N.Inputs) :
  R.v6730 (state s) (inputs i) = Zmod.unsigned (N.v6730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6730 s i)) at 1.
  unfold R.v6730, N.v6730.
  rewrite ?node_6726.
  rewrite ?node_6729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6731 (s : N.State) (i : N.Inputs) :
  R.v6731 (state s) (inputs i) = Zmod.unsigned (N.v6731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6731 s i)) at 1.
  unfold R.v6731, N.v6731.
  rewrite ?node_6613.
  rewrite !state_r347_nr_5F347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r347_nr_5F347 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6732 (s : N.State) (i : N.Inputs) :
  R.v6732 (state s) (inputs i) = Zmod.unsigned (N.v6732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6732 s i)) at 1.
  unfold R.v6732, N.v6732.
  rewrite ?node_6614.
  rewrite ?node_6617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6733 (s : N.State) (i : N.Inputs) :
  R.v6733 (state s) (inputs i) = Zmod.unsigned (N.v6733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6733 s i)) at 1.
  unfold R.v6733, N.v6733.
  rewrite ?node_6731.
  rewrite ?node_6732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6734 (s : N.State) (i : N.Inputs) :
  R.v6734 (state s) (inputs i) = Zmod.unsigned (N.v6734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6734 s i)) at 1.
  unfold R.v6734, N.v6734.
  rewrite ?node_6730.
  rewrite ?node_6733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6735 (s : N.State) (i : N.Inputs) :
  R.v6735 (state s) (inputs i) = Zmod.unsigned (N.v6735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6735 s i)) at 1.
  unfold R.v6735, N.v6735.
  rewrite ?node_6621.
  rewrite !state_r351_nr_5F351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r351_nr_5F351 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6736 (s : N.State) (i : N.Inputs) :
  R.v6736 (state s) (inputs i) = Zmod.unsigned (N.v6736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6736 s i)) at 1.
  unfold R.v6736, N.v6736.
  rewrite ?node_6622.
  rewrite ?node_6625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6737 (s : N.State) (i : N.Inputs) :
  R.v6737 (state s) (inputs i) = Zmod.unsigned (N.v6737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6737 s i)) at 1.
  unfold R.v6737, N.v6737.
  rewrite ?node_6735.
  rewrite ?node_6736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6738 (s : N.State) (i : N.Inputs) :
  R.v6738 (state s) (inputs i) = Zmod.unsigned (N.v6738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6738 s i)) at 1.
  unfold R.v6738, N.v6738.
  rewrite ?node_6734.
  rewrite ?node_6737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6739 (s : N.State) (i : N.Inputs) :
  R.v6739 (state s) (inputs i) = Zmod.unsigned (N.v6739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6739 s i)) at 1.
  unfold R.v6739, N.v6739.
  rewrite ?node_6641.
  rewrite ?node_6644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6740 (s : N.State) (i : N.Inputs) :
  R.v6740 (state s) (inputs i) = Zmod.unsigned (N.v6740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6740 s i)) at 1.
  unfold R.v6740, N.v6740.
  rewrite ?node_6645.
  rewrite ?node_6648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6741 (s : N.State) (i : N.Inputs) :
  R.v6741 (state s) (inputs i) = Zmod.unsigned (N.v6741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6741 s i)) at 1.
  unfold R.v6741, N.v6741.
  rewrite ?node_6739.
  rewrite ?node_6740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6742 (s : N.State) (i : N.Inputs) :
  R.v6742 (state s) (inputs i) = Zmod.unsigned (N.v6742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6742 s i)) at 1.
  unfold R.v6742, N.v6742.
  rewrite ?node_6738.
  rewrite ?node_6741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6743 (s : N.State) (i : N.Inputs) :
  R.v6743 (state s) (inputs i) = Zmod.unsigned (N.v6743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6743 s i)) at 1.
  unfold R.v6743, N.v6743.
  rewrite ?node_6724.
  rewrite ?node_6742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6744 (s : N.State) (i : N.Inputs) :
  R.v6744 (state s) (inputs i) = Zmod.unsigned (N.v6744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6744 s i)) at 1.
  unfold R.v6744, N.v6744.
  rewrite ?node_6629.
  rewrite !state_r355_nr_5F355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r355_nr_5F355 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6745 (s : N.State) (i : N.Inputs) :
  R.v6745 (state s) (inputs i) = Zmod.unsigned (N.v6745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6745 s i)) at 1.
  unfold R.v6745, N.v6745.
  rewrite ?node_6630.
  rewrite ?node_6633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6746 (s : N.State) (i : N.Inputs) :
  R.v6746 (state s) (inputs i) = Zmod.unsigned (N.v6746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6746 s i)) at 1.
  unfold R.v6746, N.v6746.
  rewrite ?node_6744.
  rewrite ?node_6745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6747 (s : N.State) (i : N.Inputs) :
  R.v6747 (state s) (inputs i) = Zmod.unsigned (N.v6747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6747 s i)) at 1.
  unfold R.v6747, N.v6747.
  rewrite !state_r356_nr_5F356.
  rewrite !state_r357_nr_5F357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r356_nr_5F356 s)).
  rewrite ?(bits.mod_to_Z (N.r357_nr_5F357 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6748 (s : N.State) (i : N.Inputs) :
  R.v6748 (state s) (inputs i) = Zmod.unsigned (N.v6748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6748 s i)) at 1.
  unfold R.v6748, N.v6748.
  rewrite ?node_6640.
  rewrite !state_r358_nr_5F358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r358_nr_5F358 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6749 (s : N.State) (i : N.Inputs) :
  R.v6749 (state s) (inputs i) = Zmod.unsigned (N.v6749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6749 s i)) at 1.
  unfold R.v6749, N.v6749.
  rewrite ?node_6747.
  rewrite ?node_6748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6750 (s : N.State) (i : N.Inputs) :
  R.v6750 (state s) (inputs i) = Zmod.unsigned (N.v6750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6750 s i)) at 1.
  unfold R.v6750, N.v6750.
  rewrite ?node_6746.
  rewrite ?node_6749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6751 (s : N.State) (i : N.Inputs) :
  R.v6751 (state s) (inputs i) = Zmod.unsigned (N.v6751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6751 s i)) at 1.
  unfold R.v6751, N.v6751.
  rewrite ?node_6743.
  rewrite ?node_6750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6752 (s : N.State) (i : N.Inputs) :
  R.v6752 (state s) (inputs i) = Zmod.unsigned (N.v6752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6752 s i)) at 1.
  unfold R.v6752, N.v6752.
  rewrite ?node_6627.
  rewrite ?node_6634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6753 (s : N.State) (i : N.Inputs) :
  R.v6753 (state s) (inputs i) = Zmod.unsigned (N.v6753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6753 s i)) at 1.
  unfold R.v6753, N.v6753.
  rewrite ?node_6635.
  rewrite ?node_6638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6754 (s : N.State) (i : N.Inputs) :
  R.v6754 (state s) (inputs i) = Zmod.unsigned (N.v6754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6754 s i)) at 1.
  unfold R.v6754, N.v6754.
  rewrite ?node_6752.
  rewrite ?node_6753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6755 (s : N.State) (i : N.Inputs) :
  R.v6755 (state s) (inputs i) = Zmod.unsigned (N.v6755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6755 s i)) at 1.
  unfold R.v6755, N.v6755.
  rewrite ?node_6751.
  rewrite ?node_6754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6756 (s : N.State) (i : N.Inputs) :
  R.v6756 (state s) (inputs i) = Zmod.unsigned (N.v6756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6756 s i)) at 1.
  unfold R.v6756, N.v6756.
  rewrite ?node_6639.
  rewrite ?node_6657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6757 (s : N.State) (i : N.Inputs) :
  R.v6757 (state s) (inputs i) = Zmod.unsigned (N.v6757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6757 s i)) at 1.
  unfold R.v6757, N.v6757.
  rewrite ?node_6658.
  rewrite ?node_6663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6758 (s : N.State) (i : N.Inputs) :
  R.v6758 (state s) (inputs i) = Zmod.unsigned (N.v6758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6758 s i)) at 1.
  unfold R.v6758, N.v6758.
  rewrite ?node_6756.
  rewrite ?node_6757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6759 (s : N.State) (i : N.Inputs) :
  R.v6759 (state s) (inputs i) = Zmod.unsigned (N.v6759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6759 s i)) at 1.
  unfold R.v6759, N.v6759.
  rewrite ?node_6755.
  rewrite ?node_6758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6760 (s : N.State) (i : N.Inputs) :
  R.v6760 (state s) (inputs i) = Zmod.unsigned (N.v6760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6760 s i)) at 1.
  unfold R.v6760, N.v6760.
  rewrite ?node_6649.
  rewrite ?node_6652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6761 (s : N.State) (i : N.Inputs) :
  R.v6761 (state s) (inputs i) = Zmod.unsigned (N.v6761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6761 s i)) at 1.
  unfold R.v6761, N.v6761.
  rewrite ?node_6653.
  rewrite ?node_6656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6762 (s : N.State) (i : N.Inputs) :
  R.v6762 (state s) (inputs i) = Zmod.unsigned (N.v6762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6762 s i)) at 1.
  unfold R.v6762, N.v6762.
  rewrite ?node_6760.
  rewrite ?node_6761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6763 (s : N.State) (i : N.Inputs) :
  R.v6763 (state s) (inputs i) = Zmod.unsigned (N.v6763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6763 s i)) at 1.
  unfold R.v6763, N.v6763.
  rewrite ?node_6661.
  rewrite ?node_6662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6764 (s : N.State) (i : N.Inputs) :
  R.v6764 (state s) (inputs i) = Zmod.unsigned (N.v6764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6764 s i)) at 1.
  unfold R.v6764, N.v6764.
  rewrite ?node_6762.
  rewrite ?node_6763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6765 (s : N.State) (i : N.Inputs) :
  R.v6765 (state s) (inputs i) = Zmod.unsigned (N.v6765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6765 s i)) at 1.
  unfold R.v6765, N.v6765.
  rewrite ?node_6759.
  rewrite ?node_6764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6766 (s : N.State) (i : N.Inputs) :
  R.v6766 (state s) (inputs i) = Zmod.unsigned (N.v6766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6766 s i)) at 1.
  unfold R.v6766, N.v6766.
  rewrite ?node_6664.
  rewrite ?node_6667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6767 (s : N.State) (i : N.Inputs) :
  R.v6767 (state s) (inputs i) = Zmod.unsigned (N.v6767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6767 s i)) at 1.
  unfold R.v6767, N.v6767.
  rewrite ?node_6668.
  rewrite ?node_6671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6768 (s : N.State) (i : N.Inputs) :
  R.v6768 (state s) (inputs i) = Zmod.unsigned (N.v6768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6768 s i)) at 1.
  unfold R.v6768, N.v6768.
  rewrite ?node_6766.
  rewrite ?node_6767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6769 (s : N.State) (i : N.Inputs) :
  R.v6769 (state s) (inputs i) = Zmod.unsigned (N.v6769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6769 s i)) at 1.
  unfold R.v6769, N.v6769.
  rewrite ?node_6765.
  rewrite ?node_6768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6770 (s : N.State) (i : N.Inputs) :
  R.v6770 (state s) (inputs i) = Zmod.unsigned (N.v6770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6770 s i)) at 1.
  unfold R.v6770, N.v6770.
  rewrite ?node_6675.
  rewrite ?node_6676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6771 (s : N.State) (i : N.Inputs) :
  R.v6771 (state s) (inputs i) = Zmod.unsigned (N.v6771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6771 s i)) at 1.
  unfold R.v6771, N.v6771.
  rewrite ?node_6769.
  rewrite ?node_6770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6772 (s : N.State) (i : N.Inputs) :
  R.v6772 (state s) (inputs i) = Zmod.unsigned (N.v6772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6772 s i)) at 1.
  unfold R.v6772, N.v6772.
  rewrite ?node_6672.
  rewrite ?node_6677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6773 (s : N.State) (i : N.Inputs) :
  R.v6773 (state s) (inputs i) = Zmod.unsigned (N.v6773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6773 s i)) at 1.
  unfold R.v6773, N.v6773.
  rewrite ?node_6678.
  rewrite ?node_6681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6774 (s : N.State) (i : N.Inputs) :
  R.v6774 (state s) (inputs i) = Zmod.unsigned (N.v6774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6774 s i)) at 1.
  unfold R.v6774, N.v6774.
  rewrite ?node_6772.
  rewrite ?node_6773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6775 (s : N.State) (i : N.Inputs) :
  R.v6775 (state s) (inputs i) = Zmod.unsigned (N.v6775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6775 s i)) at 1.
  unfold R.v6775, N.v6775.
  rewrite ?node_6771.
  rewrite ?node_6774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6776 (s : N.State) (i : N.Inputs) :
  R.v6776 (state s) (inputs i) = Zmod.unsigned (N.v6776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6776 s i)) at 1.
  unfold R.v6776, N.v6776.
  rewrite ?node_6775.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2343_nr_5F2374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2343_nr_5F2374 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6777 (s : N.State) (i : N.Inputs) :
  R.v6777 (state s) (inputs i) = Zmod.unsigned (N.v6777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6777 s i)) at 1.
  unfold R.v6777, N.v6777.
  rewrite ?node_6682.
  rewrite ?node_6685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6778 (s : N.State) (i : N.Inputs) :
  R.v6778 (state s) (inputs i) = Zmod.unsigned (N.v6778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6778 s i)) at 1.
  unfold R.v6778, N.v6778.
  rewrite ?node_6777.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2344_nr_5F2375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2344_nr_5F2375 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6779 (s : N.State) (i : N.Inputs) :
  R.v6779 (state s) (inputs i) = Zmod.unsigned (N.v6779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6779 s i)) at 1.
  unfold R.v6779, N.v6779.
  rewrite !state_r378_nr_5F378.
  rewrite !state_r379_nr_5F379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r378_nr_5F378 s)).
  rewrite ?(bits.mod_to_Z (N.r379_nr_5F379 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6780 (s : N.State) (i : N.Inputs) :
  R.v6780 (state s) (inputs i) = Zmod.unsigned (N.v6780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6780 s i)) at 1.
  unfold R.v6780, N.v6780.
  rewrite ?node_6779.
  rewrite !state_r380_nr_5F380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r380_nr_5F380 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6781 (s : N.State) (i : N.Inputs) :
  R.v6781 (state s) (inputs i) = Zmod.unsigned (N.v6781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6781 s i)) at 1.
  unfold R.v6781, N.v6781.
  rewrite ?node_6780.
  rewrite !state_r381_nr_5F381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r381_nr_5F381 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6782 (s : N.State) (i : N.Inputs) :
  R.v6782 (state s) (inputs i) = Zmod.unsigned (N.v6782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6782 s i)) at 1.
  unfold R.v6782, N.v6782.
  rewrite !state_r359_nr_5F359.
  rewrite !state_r360_nr_5F360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r359_nr_5F359 s)).
  rewrite ?(bits.mod_to_Z (N.r360_nr_5F360 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6783 (s : N.State) (i : N.Inputs) :
  R.v6783 (state s) (inputs i) = Zmod.unsigned (N.v6783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6783 s i)) at 1.
  unfold R.v6783, N.v6783.
  rewrite ?node_6690.
  rewrite !state_r361_nr_5F361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r361_nr_5F361 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6784 (s : N.State) (i : N.Inputs) :
  R.v6784 (state s) (inputs i) = Zmod.unsigned (N.v6784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6784 s i)) at 1.
  unfold R.v6784, N.v6784.
  rewrite ?node_6782.
  rewrite ?node_6783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6785 (s : N.State) (i : N.Inputs) :
  R.v6785 (state s) (inputs i) = Zmod.unsigned (N.v6785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6785 s i)) at 1.
  unfold R.v6785, N.v6785.
  rewrite ?node_6781.
  rewrite ?node_6784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6786 (s : N.State) (i : N.Inputs) :
  R.v6786 (state s) (inputs i) = Zmod.unsigned (N.v6786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6786 s i)) at 1.
  unfold R.v6786, N.v6786.
  rewrite !state_r382_nr_5F382.
  rewrite !state_r383_nr_5F383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r382_nr_5F382 s)).
  rewrite ?(bits.mod_to_Z (N.r383_nr_5F383 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6787 (s : N.State) (i : N.Inputs) :
  R.v6787 (state s) (inputs i) = Zmod.unsigned (N.v6787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6787 s i)) at 1.
  unfold R.v6787, N.v6787.
  rewrite ?node_6786.
  rewrite !state_r384_nr_5F384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r384_nr_5F384 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6788 (s : N.State) (i : N.Inputs) :
  R.v6788 (state s) (inputs i) = Zmod.unsigned (N.v6788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6788 s i)) at 1.
  unfold R.v6788, N.v6788.
  rewrite ?node_6787.
  rewrite !state_r385_nr_5F385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r385_nr_5F385 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6789 (s : N.State) (i : N.Inputs) :
  R.v6789 (state s) (inputs i) = Zmod.unsigned (N.v6789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6789 s i)) at 1.
  unfold R.v6789, N.v6789.
  rewrite !state_r363_nr_5F363.
  rewrite !state_r364_nr_5F364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r363_nr_5F363 s)).
  rewrite ?(bits.mod_to_Z (N.r364_nr_5F364 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6790 (s : N.State) (i : N.Inputs) :
  R.v6790 (state s) (inputs i) = Zmod.unsigned (N.v6790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6790 s i)) at 1.
  unfold R.v6790, N.v6790.
  rewrite ?node_6697.
  rewrite !state_r365_nr_5F365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r365_nr_5F365 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6791 (s : N.State) (i : N.Inputs) :
  R.v6791 (state s) (inputs i) = Zmod.unsigned (N.v6791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6791 s i)) at 1.
  unfold R.v6791, N.v6791.
  rewrite ?node_6789.
  rewrite ?node_6790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6792 (s : N.State) (i : N.Inputs) :
  R.v6792 (state s) (inputs i) = Zmod.unsigned (N.v6792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6792 s i)) at 1.
  unfold R.v6792, N.v6792.
  rewrite ?node_6788.
  rewrite ?node_6791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6793 (s : N.State) (i : N.Inputs) :
  R.v6793 (state s) (inputs i) = Zmod.unsigned (N.v6793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6793 s i)) at 1.
  unfold R.v6793, N.v6793.
  rewrite ?node_6785.
  rewrite ?node_6792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6794 (s : N.State) (i : N.Inputs) :
  R.v6794 (state s) (inputs i) = Zmod.unsigned (N.v6794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6794 s i)) at 1.
  unfold R.v6794, N.v6794.
  rewrite !state_r386_nr_5F386.
  rewrite !state_r387_nr_5F387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r386_nr_5F386 s)).
  rewrite ?(bits.mod_to_Z (N.r387_nr_5F387 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6795 (s : N.State) (i : N.Inputs) :
  R.v6795 (state s) (inputs i) = Zmod.unsigned (N.v6795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6795 s i)) at 1.
  unfold R.v6795, N.v6795.
  rewrite ?node_6794.
  rewrite !state_r388_nr_5F388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r388_nr_5F388 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6796 (s : N.State) (i : N.Inputs) :
  R.v6796 (state s) (inputs i) = Zmod.unsigned (N.v6796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6796 s i)) at 1.
  unfold R.v6796, N.v6796.
  rewrite ?node_6795.
  rewrite !state_r389_nr_5F389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r389_nr_5F389 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6797 (s : N.State) (i : N.Inputs) :
  R.v6797 (state s) (inputs i) = Zmod.unsigned (N.v6797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6797 s i)) at 1.
  unfold R.v6797, N.v6797.
  rewrite !state_r367_nr_5F367.
  rewrite !state_r368_nr_5F368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r367_nr_5F367 s)).
  rewrite ?(bits.mod_to_Z (N.r368_nr_5F368 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6798 (s : N.State) (i : N.Inputs) :
  R.v6798 (state s) (inputs i) = Zmod.unsigned (N.v6798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6798 s i)) at 1.
  unfold R.v6798, N.v6798.
  rewrite ?node_6705.
  rewrite !state_r369_nr_5F369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r369_nr_5F369 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6799 (s : N.State) (i : N.Inputs) :
  R.v6799 (state s) (inputs i) = Zmod.unsigned (N.v6799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6799 s i)) at 1.
  unfold R.v6799, N.v6799.
  rewrite ?node_6797.
  rewrite ?node_6798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6800 (s : N.State) (i : N.Inputs) :
  R.v6800 (state s) (inputs i) = Zmod.unsigned (N.v6800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6800 s i)) at 1.
  unfold R.v6800, N.v6800.
  rewrite ?node_6796.
  rewrite ?node_6799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6801 (s : N.State) (i : N.Inputs) :
  R.v6801 (state s) (inputs i) = Zmod.unsigned (N.v6801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6801 s i)) at 1.
  unfold R.v6801, N.v6801.
  rewrite ?node_6793.
  rewrite ?node_6800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6802 (s : N.State) (i : N.Inputs) :
  R.v6802 (state s) (inputs i) = Zmod.unsigned (N.v6802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6802 s i)) at 1.
  unfold R.v6802, N.v6802.
  rewrite !state_r390_nr_5F390.
  rewrite !state_r391_nr_5F391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r390_nr_5F390 s)).
  rewrite ?(bits.mod_to_Z (N.r391_nr_5F391 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6803 (s : N.State) (i : N.Inputs) :
  R.v6803 (state s) (inputs i) = Zmod.unsigned (N.v6803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6803 s i)) at 1.
  unfold R.v6803, N.v6803.
  rewrite ?node_6802.
  rewrite !state_r392_nr_5F392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r392_nr_5F392 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6804 (s : N.State) (i : N.Inputs) :
  R.v6804 (state s) (inputs i) = Zmod.unsigned (N.v6804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6804 s i)) at 1.
  unfold R.v6804, N.v6804.
  rewrite ?node_6803.
  rewrite !state_r393_nr_5F393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r393_nr_5F393 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6805 (s : N.State) (i : N.Inputs) :
  R.v6805 (state s) (inputs i) = Zmod.unsigned (N.v6805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6805 s i)) at 1.
  unfold R.v6805, N.v6805.
  rewrite !state_r371_nr_5F371.
  rewrite !state_r372_nr_5F372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r371_nr_5F371 s)).
  rewrite ?(bits.mod_to_Z (N.r372_nr_5F372 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6806 (s : N.State) (i : N.Inputs) :
  R.v6806 (state s) (inputs i) = Zmod.unsigned (N.v6806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6806 s i)) at 1.
  unfold R.v6806, N.v6806.
  rewrite ?node_6713.
  rewrite !state_r373_nr_5F373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r373_nr_5F373 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6807 (s : N.State) (i : N.Inputs) :
  R.v6807 (state s) (inputs i) = Zmod.unsigned (N.v6807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6807 s i)) at 1.
  unfold R.v6807, N.v6807.
  rewrite ?node_6805.
  rewrite ?node_6806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6808 (s : N.State) (i : N.Inputs) :
  R.v6808 (state s) (inputs i) = Zmod.unsigned (N.v6808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6808 s i)) at 1.
  unfold R.v6808, N.v6808.
  rewrite ?node_6804.
  rewrite ?node_6807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6809 (s : N.State) (i : N.Inputs) :
  R.v6809 (state s) (inputs i) = Zmod.unsigned (N.v6809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6809 s i)) at 1.
  unfold R.v6809, N.v6809.
  rewrite ?node_6801.
  rewrite ?node_6808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6810 (s : N.State) (i : N.Inputs) :
  R.v6810 (state s) (inputs i) = Zmod.unsigned (N.v6810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6810 s i)) at 1.
  unfold R.v6810, N.v6810.
  rewrite ?node_6696.
  rewrite ?node_6703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6811 (s : N.State) (i : N.Inputs) :
  R.v6811 (state s) (inputs i) = Zmod.unsigned (N.v6811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6811 s i)) at 1.
  unfold R.v6811, N.v6811.
  rewrite ?node_6704.
  rewrite ?node_6711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6812 (s : N.State) (i : N.Inputs) :
  R.v6812 (state s) (inputs i) = Zmod.unsigned (N.v6812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6812 s i)) at 1.
  unfold R.v6812, N.v6812.
  rewrite ?node_6810.
  rewrite ?node_6811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6813 (s : N.State) (i : N.Inputs) :
  R.v6813 (state s) (inputs i) = Zmod.unsigned (N.v6813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6813 s i)) at 1.
  unfold R.v6813, N.v6813.
  rewrite ?node_6809.
  rewrite ?node_6812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6814 (s : N.State) (i : N.Inputs) :
  R.v6814 (state s) (inputs i) = Zmod.unsigned (N.v6814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6814 s i)) at 1.
  unfold R.v6814, N.v6814.
  rewrite !state_r394_nr_5F394.
  rewrite !state_r395_nr_5F395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r394_nr_5F394 s)).
  rewrite ?(bits.mod_to_Z (N.r395_nr_5F395 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6815 (s : N.State) (i : N.Inputs) :
  R.v6815 (state s) (inputs i) = Zmod.unsigned (N.v6815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6815 s i)) at 1.
  unfold R.v6815, N.v6815.
  rewrite ?node_6814.
  rewrite !state_r396_nr_5F396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r396_nr_5F396 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6816 (s : N.State) (i : N.Inputs) :
  R.v6816 (state s) (inputs i) = Zmod.unsigned (N.v6816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6816 s i)) at 1.
  unfold R.v6816, N.v6816.
  rewrite ?node_6815.
  rewrite !state_r397_nr_5F397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r397_nr_5F397 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6817 (s : N.State) (i : N.Inputs) :
  R.v6817 (state s) (inputs i) = Zmod.unsigned (N.v6817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6817 s i)) at 1.
  unfold R.v6817, N.v6817.
  rewrite ?node_6691.
  rewrite !state_r362_nr_5F362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r362_nr_5F362 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6818 (s : N.State) (i : N.Inputs) :
  R.v6818 (state s) (inputs i) = Zmod.unsigned (N.v6818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6818 s i)) at 1.
  unfold R.v6818, N.v6818.
  rewrite ?node_6692.
  rewrite ?node_6695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6819 (s : N.State) (i : N.Inputs) :
  R.v6819 (state s) (inputs i) = Zmod.unsigned (N.v6819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6819 s i)) at 1.
  unfold R.v6819, N.v6819.
  rewrite ?node_6817.
  rewrite ?node_6818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6820 (s : N.State) (i : N.Inputs) :
  R.v6820 (state s) (inputs i) = Zmod.unsigned (N.v6820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6820 s i)) at 1.
  unfold R.v6820, N.v6820.
  rewrite ?node_6816.
  rewrite ?node_6819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6821 (s : N.State) (i : N.Inputs) :
  R.v6821 (state s) (inputs i) = Zmod.unsigned (N.v6821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6821 s i)) at 1.
  unfold R.v6821, N.v6821.
  rewrite ?node_6698.
  rewrite !state_r366_nr_5F366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r366_nr_5F366 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6822 (s : N.State) (i : N.Inputs) :
  R.v6822 (state s) (inputs i) = Zmod.unsigned (N.v6822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6822 s i)) at 1.
  unfold R.v6822, N.v6822.
  rewrite ?node_6699.
  rewrite ?node_6702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6823 (s : N.State) (i : N.Inputs) :
  R.v6823 (state s) (inputs i) = Zmod.unsigned (N.v6823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6823 s i)) at 1.
  unfold R.v6823, N.v6823.
  rewrite ?node_6821.
  rewrite ?node_6822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6824 (s : N.State) (i : N.Inputs) :
  R.v6824 (state s) (inputs i) = Zmod.unsigned (N.v6824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6824 s i)) at 1.
  unfold R.v6824, N.v6824.
  rewrite ?node_6820.
  rewrite ?node_6823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6825 (s : N.State) (i : N.Inputs) :
  R.v6825 (state s) (inputs i) = Zmod.unsigned (N.v6825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6825 s i)) at 1.
  unfold R.v6825, N.v6825.
  rewrite ?node_6706.
  rewrite !state_r370_nr_5F370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r370_nr_5F370 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6826 (s : N.State) (i : N.Inputs) :
  R.v6826 (state s) (inputs i) = Zmod.unsigned (N.v6826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6826 s i)) at 1.
  unfold R.v6826, N.v6826.
  rewrite ?node_6707.
  rewrite ?node_6710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6827 (s : N.State) (i : N.Inputs) :
  R.v6827 (state s) (inputs i) = Zmod.unsigned (N.v6827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6827 s i)) at 1.
  unfold R.v6827, N.v6827.
  rewrite ?node_6825.
  rewrite ?node_6826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6828 (s : N.State) (i : N.Inputs) :
  R.v6828 (state s) (inputs i) = Zmod.unsigned (N.v6828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6828 s i)) at 1.
  unfold R.v6828, N.v6828.
  rewrite ?node_6824.
  rewrite ?node_6827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6829 (s : N.State) (i : N.Inputs) :
  R.v6829 (state s) (inputs i) = Zmod.unsigned (N.v6829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6829 s i)) at 1.
  unfold R.v6829, N.v6829.
  rewrite ?node_6726.
  rewrite ?node_6729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6830 (s : N.State) (i : N.Inputs) :
  R.v6830 (state s) (inputs i) = Zmod.unsigned (N.v6830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6830 s i)) at 1.
  unfold R.v6830, N.v6830.
  rewrite ?node_6730.
  rewrite ?node_6733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6831 (s : N.State) (i : N.Inputs) :
  R.v6831 (state s) (inputs i) = Zmod.unsigned (N.v6831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6831 s i)) at 1.
  unfold R.v6831, N.v6831.
  rewrite ?node_6829.
  rewrite ?node_6830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6832 (s : N.State) (i : N.Inputs) :
  R.v6832 (state s) (inputs i) = Zmod.unsigned (N.v6832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6832 s i)) at 1.
  unfold R.v6832, N.v6832.
  rewrite ?node_6828.
  rewrite ?node_6831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6833 (s : N.State) (i : N.Inputs) :
  R.v6833 (state s) (inputs i) = Zmod.unsigned (N.v6833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6833 s i)) at 1.
  unfold R.v6833, N.v6833.
  rewrite ?node_6813.
  rewrite ?node_6832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6834 (s : N.State) (i : N.Inputs) :
  R.v6834 (state s) (inputs i) = Zmod.unsigned (N.v6834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6834 s i)) at 1.
  unfold R.v6834, N.v6834.
  rewrite ?node_6714.
  rewrite !state_r374_nr_5F374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r374_nr_5F374 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6835 (s : N.State) (i : N.Inputs) :
  R.v6835 (state s) (inputs i) = Zmod.unsigned (N.v6835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6835 s i)) at 1.
  unfold R.v6835, N.v6835.
  rewrite ?node_6715.
  rewrite ?node_6718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6836 (s : N.State) (i : N.Inputs) :
  R.v6836 (state s) (inputs i) = Zmod.unsigned (N.v6836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6836 s i)) at 1.
  unfold R.v6836, N.v6836.
  rewrite ?node_6834.
  rewrite ?node_6835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6837 (s : N.State) (i : N.Inputs) :
  R.v6837 (state s) (inputs i) = Zmod.unsigned (N.v6837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6837 s i)) at 1.
  unfold R.v6837, N.v6837.
  rewrite !state_r375_nr_5F375.
  rewrite !state_r376_nr_5F376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r375_nr_5F375 s)).
  rewrite ?(bits.mod_to_Z (N.r376_nr_5F376 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6838 (s : N.State) (i : N.Inputs) :
  R.v6838 (state s) (inputs i) = Zmod.unsigned (N.v6838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6838 s i)) at 1.
  unfold R.v6838, N.v6838.
  rewrite ?node_6725.
  rewrite !state_r377_nr_5F377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r377_nr_5F377 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6839 (s : N.State) (i : N.Inputs) :
  R.v6839 (state s) (inputs i) = Zmod.unsigned (N.v6839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6839 s i)) at 1.
  unfold R.v6839, N.v6839.
  rewrite ?node_6837.
  rewrite ?node_6838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6840 (s : N.State) (i : N.Inputs) :
  R.v6840 (state s) (inputs i) = Zmod.unsigned (N.v6840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6840 s i)) at 1.
  unfold R.v6840, N.v6840.
  rewrite ?node_6836.
  rewrite ?node_6839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6841 (s : N.State) (i : N.Inputs) :
  R.v6841 (state s) (inputs i) = Zmod.unsigned (N.v6841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6841 s i)) at 1.
  unfold R.v6841, N.v6841.
  rewrite ?node_6833.
  rewrite ?node_6840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6842 (s : N.State) (i : N.Inputs) :
  R.v6842 (state s) (inputs i) = Zmod.unsigned (N.v6842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6842 s i)) at 1.
  unfold R.v6842, N.v6842.
  rewrite ?node_6712.
  rewrite ?node_6719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6843 (s : N.State) (i : N.Inputs) :
  R.v6843 (state s) (inputs i) = Zmod.unsigned (N.v6843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6843 s i)) at 1.
  unfold R.v6843, N.v6843.
  rewrite ?node_6720.
  rewrite ?node_6723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6844 (s : N.State) (i : N.Inputs) :
  R.v6844 (state s) (inputs i) = Zmod.unsigned (N.v6844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6844 s i)) at 1.
  unfold R.v6844, N.v6844.
  rewrite ?node_6842.
  rewrite ?node_6843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6845 (s : N.State) (i : N.Inputs) :
  R.v6845 (state s) (inputs i) = Zmod.unsigned (N.v6845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6845 s i)) at 1.
  unfold R.v6845, N.v6845.
  rewrite ?node_6841.
  rewrite ?node_6844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6846 (s : N.State) (i : N.Inputs) :
  R.v6846 (state s) (inputs i) = Zmod.unsigned (N.v6846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6846 s i)) at 1.
  unfold R.v6846, N.v6846.
  rewrite ?node_6724.
  rewrite ?node_6742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6847 (s : N.State) (i : N.Inputs) :
  R.v6847 (state s) (inputs i) = Zmod.unsigned (N.v6847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6847 s i)) at 1.
  unfold R.v6847, N.v6847.
  rewrite ?node_6743.
  rewrite ?node_6750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6848 (s : N.State) (i : N.Inputs) :
  R.v6848 (state s) (inputs i) = Zmod.unsigned (N.v6848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6848 s i)) at 1.
  unfold R.v6848, N.v6848.
  rewrite ?node_6846.
  rewrite ?node_6847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6849 (s : N.State) (i : N.Inputs) :
  R.v6849 (state s) (inputs i) = Zmod.unsigned (N.v6849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6849 s i)) at 1.
  unfold R.v6849, N.v6849.
  rewrite ?node_6845.
  rewrite ?node_6848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6850 (s : N.State) (i : N.Inputs) :
  R.v6850 (state s) (inputs i) = Zmod.unsigned (N.v6850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6850 s i)) at 1.
  unfold R.v6850, N.v6850.
  rewrite ?node_6734.
  rewrite ?node_6737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6851 (s : N.State) (i : N.Inputs) :
  R.v6851 (state s) (inputs i) = Zmod.unsigned (N.v6851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6851 s i)) at 1.
  unfold R.v6851, N.v6851.
  rewrite ?node_6738.
  rewrite ?node_6741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6852 (s : N.State) (i : N.Inputs) :
  R.v6852 (state s) (inputs i) = Zmod.unsigned (N.v6852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6852 s i)) at 1.
  unfold R.v6852, N.v6852.
  rewrite ?node_6850.
  rewrite ?node_6851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6853 (s : N.State) (i : N.Inputs) :
  R.v6853 (state s) (inputs i) = Zmod.unsigned (N.v6853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6853 s i)) at 1.
  unfold R.v6853, N.v6853.
  rewrite ?node_6746.
  rewrite ?node_6749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6854 (s : N.State) (i : N.Inputs) :
  R.v6854 (state s) (inputs i) = Zmod.unsigned (N.v6854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6854 s i)) at 1.
  unfold R.v6854, N.v6854.
  rewrite ?node_6852.
  rewrite ?node_6853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6855 (s : N.State) (i : N.Inputs) :
  R.v6855 (state s) (inputs i) = Zmod.unsigned (N.v6855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6855 s i)) at 1.
  unfold R.v6855, N.v6855.
  rewrite ?node_6849.
  rewrite ?node_6854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6856 (s : N.State) (i : N.Inputs) :
  R.v6856 (state s) (inputs i) = Zmod.unsigned (N.v6856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6856 s i)) at 1.
  unfold R.v6856, N.v6856.
  rewrite ?node_6751.
  rewrite ?node_6754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6857 (s : N.State) (i : N.Inputs) :
  R.v6857 (state s) (inputs i) = Zmod.unsigned (N.v6857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6857 s i)) at 1.
  unfold R.v6857, N.v6857.
  rewrite ?node_6755.
  rewrite ?node_6758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6858 (s : N.State) (i : N.Inputs) :
  R.v6858 (state s) (inputs i) = Zmod.unsigned (N.v6858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6858 s i)) at 1.
  unfold R.v6858, N.v6858.
  rewrite ?node_6856.
  rewrite ?node_6857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6859 (s : N.State) (i : N.Inputs) :
  R.v6859 (state s) (inputs i) = Zmod.unsigned (N.v6859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6859 s i)) at 1.
  unfold R.v6859, N.v6859.
  rewrite ?node_6855.
  rewrite ?node_6858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6860 (s : N.State) (i : N.Inputs) :
  R.v6860 (state s) (inputs i) = Zmod.unsigned (N.v6860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6860 s i)) at 1.
  unfold R.v6860, N.v6860.
  rewrite ?node_6762.
  rewrite ?node_6763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6861 (s : N.State) (i : N.Inputs) :
  R.v6861 (state s) (inputs i) = Zmod.unsigned (N.v6861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6861 s i)) at 1.
  unfold R.v6861, N.v6861.
  rewrite ?node_6859.
  rewrite ?node_6860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6862 (s : N.State) (i : N.Inputs) :
  R.v6862 (state s) (inputs i) = Zmod.unsigned (N.v6862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6862 s i)) at 1.
  unfold R.v6862, N.v6862.
  rewrite ?node_6759.
  rewrite ?node_6764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6863 (s : N.State) (i : N.Inputs) :
  R.v6863 (state s) (inputs i) = Zmod.unsigned (N.v6863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6863 s i)) at 1.
  unfold R.v6863, N.v6863.
  rewrite ?node_6765.
  rewrite ?node_6768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6864 (s : N.State) (i : N.Inputs) :
  R.v6864 (state s) (inputs i) = Zmod.unsigned (N.v6864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6864 s i)) at 1.
  unfold R.v6864, N.v6864.
  rewrite ?node_6862.
  rewrite ?node_6863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6865 (s : N.State) (i : N.Inputs) :
  R.v6865 (state s) (inputs i) = Zmod.unsigned (N.v6865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6865 s i)) at 1.
  unfold R.v6865, N.v6865.
  rewrite ?node_6861.
  rewrite ?node_6864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6866 (s : N.State) (i : N.Inputs) :
  R.v6866 (state s) (inputs i) = Zmod.unsigned (N.v6866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6866 s i)) at 1.
  unfold R.v6866, N.v6866.
  rewrite ?node_6769.
  rewrite ?node_6770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6867 (s : N.State) (i : N.Inputs) :
  R.v6867 (state s) (inputs i) = Zmod.unsigned (N.v6867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6867 s i)) at 1.
  unfold R.v6867, N.v6867.
  rewrite ?node_6865.
  rewrite ?node_6866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6868 (s : N.State) (i : N.Inputs) :
  R.v6868 (state s) (inputs i) = Zmod.unsigned (N.v6868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6868 s i)) at 1.
  unfold R.v6868, N.v6868.
  rewrite ?node_6867.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2345_nr_5F2376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2345_nr_5F2376 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6869 (s : N.State) (i : N.Inputs) :
  R.v6869 (state s) (inputs i) = Zmod.unsigned (N.v6869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6869 s i)) at 1.
  unfold R.v6869, N.v6869.
  rewrite ?node_6771.
  rewrite ?node_6774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6870 (s : N.State) (i : N.Inputs) :
  R.v6870 (state s) (inputs i) = Zmod.unsigned (N.v6870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6870 s i)) at 1.
  unfold R.v6870, N.v6870.
  rewrite ?node_6869.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2346_nr_5F2377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2346_nr_5F2377 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6871 (s : N.State) (i : N.Inputs) :
  R.v6871 (state s) (inputs i) = Zmod.unsigned (N.v6871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6871 s i)) at 1.
  unfold R.v6871, N.v6871.
  rewrite !state_r398_nr_5F398.
  rewrite !state_r399_nr_5F399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r398_nr_5F398 s)).
  rewrite ?(bits.mod_to_Z (N.r399_nr_5F399 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6872 (s : N.State) (i : N.Inputs) :
  R.v6872 (state s) (inputs i) = Zmod.unsigned (N.v6872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6872 s i)) at 1.
  unfold R.v6872, N.v6872.
  rewrite ?node_6871.
  rewrite !state_r400_nr_5F400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r400_nr_5F400 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6873 (s : N.State) (i : N.Inputs) :
  R.v6873 (state s) (inputs i) = Zmod.unsigned (N.v6873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6873 s i)) at 1.
  unfold R.v6873, N.v6873.
  rewrite ?node_6872.
  rewrite !state_r401_nr_5F401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r401_nr_5F401 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6874 (s : N.State) (i : N.Inputs) :
  R.v6874 (state s) (inputs i) = Zmod.unsigned (N.v6874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6874 s i)) at 1.
  unfold R.v6874, N.v6874.
  rewrite !state_r378_nr_5F378.
  rewrite !state_r379_nr_5F379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r378_nr_5F378 s)).
  rewrite ?(bits.mod_to_Z (N.r379_nr_5F379 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6875 (s : N.State) (i : N.Inputs) :
  R.v6875 (state s) (inputs i) = Zmod.unsigned (N.v6875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6875 s i)) at 1.
  unfold R.v6875, N.v6875.
  rewrite ?node_6779.
  rewrite !state_r380_nr_5F380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r380_nr_5F380 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6876 (s : N.State) (i : N.Inputs) :
  R.v6876 (state s) (inputs i) = Zmod.unsigned (N.v6876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6876 s i)) at 1.
  unfold R.v6876, N.v6876.
  rewrite ?node_6874.
  rewrite ?node_6875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6877 (s : N.State) (i : N.Inputs) :
  R.v6877 (state s) (inputs i) = Zmod.unsigned (N.v6877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6877 s i)) at 1.
  unfold R.v6877, N.v6877.
  rewrite ?node_6873.
  rewrite ?node_6876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6878 (s : N.State) (i : N.Inputs) :
  R.v6878 (state s) (inputs i) = Zmod.unsigned (N.v6878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6878 s i)) at 1.
  unfold R.v6878, N.v6878.
  rewrite !state_r402_nr_5F402.
  rewrite !state_r403_nr_5F403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r402_nr_5F402 s)).
  rewrite ?(bits.mod_to_Z (N.r403_nr_5F403 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6879 (s : N.State) (i : N.Inputs) :
  R.v6879 (state s) (inputs i) = Zmod.unsigned (N.v6879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6879 s i)) at 1.
  unfold R.v6879, N.v6879.
  rewrite ?node_6878.
  rewrite !state_r404_nr_5F404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r404_nr_5F404 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6880 (s : N.State) (i : N.Inputs) :
  R.v6880 (state s) (inputs i) = Zmod.unsigned (N.v6880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6880 s i)) at 1.
  unfold R.v6880, N.v6880.
  rewrite ?node_6879.
  rewrite !state_r405_nr_5F405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r405_nr_5F405 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6881 (s : N.State) (i : N.Inputs) :
  R.v6881 (state s) (inputs i) = Zmod.unsigned (N.v6881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6881 s i)) at 1.
  unfold R.v6881, N.v6881.
  rewrite !state_r382_nr_5F382.
  rewrite !state_r383_nr_5F383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r382_nr_5F382 s)).
  rewrite ?(bits.mod_to_Z (N.r383_nr_5F383 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6882 (s : N.State) (i : N.Inputs) :
  R.v6882 (state s) (inputs i) = Zmod.unsigned (N.v6882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6882 s i)) at 1.
  unfold R.v6882, N.v6882.
  rewrite ?node_6786.
  rewrite !state_r384_nr_5F384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r384_nr_5F384 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6883 (s : N.State) (i : N.Inputs) :
  R.v6883 (state s) (inputs i) = Zmod.unsigned (N.v6883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6883 s i)) at 1.
  unfold R.v6883, N.v6883.
  rewrite ?node_6881.
  rewrite ?node_6882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6884 (s : N.State) (i : N.Inputs) :
  R.v6884 (state s) (inputs i) = Zmod.unsigned (N.v6884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6884 s i)) at 1.
  unfold R.v6884, N.v6884.
  rewrite ?node_6880.
  rewrite ?node_6883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6885 (s : N.State) (i : N.Inputs) :
  R.v6885 (state s) (inputs i) = Zmod.unsigned (N.v6885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6885 s i)) at 1.
  unfold R.v6885, N.v6885.
  rewrite ?node_6877.
  rewrite ?node_6884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6886 (s : N.State) (i : N.Inputs) :
  R.v6886 (state s) (inputs i) = Zmod.unsigned (N.v6886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6886 s i)) at 1.
  unfold R.v6886, N.v6886.
  rewrite !state_r406_nr_5F406.
  rewrite !state_r407_nr_5F407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r406_nr_5F406 s)).
  rewrite ?(bits.mod_to_Z (N.r407_nr_5F407 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6887 (s : N.State) (i : N.Inputs) :
  R.v6887 (state s) (inputs i) = Zmod.unsigned (N.v6887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6887 s i)) at 1.
  unfold R.v6887, N.v6887.
  rewrite ?node_6886.
  rewrite !state_r408_nr_5F408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r408_nr_5F408 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6888 (s : N.State) (i : N.Inputs) :
  R.v6888 (state s) (inputs i) = Zmod.unsigned (N.v6888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6888 s i)) at 1.
  unfold R.v6888, N.v6888.
  rewrite ?node_6887.
  rewrite !state_r409_nr_5F409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r409_nr_5F409 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6889 (s : N.State) (i : N.Inputs) :
  R.v6889 (state s) (inputs i) = Zmod.unsigned (N.v6889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6889 s i)) at 1.
  unfold R.v6889, N.v6889.
  rewrite !state_r386_nr_5F386.
  rewrite !state_r387_nr_5F387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r386_nr_5F386 s)).
  rewrite ?(bits.mod_to_Z (N.r387_nr_5F387 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6890 (s : N.State) (i : N.Inputs) :
  R.v6890 (state s) (inputs i) = Zmod.unsigned (N.v6890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6890 s i)) at 1.
  unfold R.v6890, N.v6890.
  rewrite ?node_6794.
  rewrite !state_r388_nr_5F388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r388_nr_5F388 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6891 (s : N.State) (i : N.Inputs) :
  R.v6891 (state s) (inputs i) = Zmod.unsigned (N.v6891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6891 s i)) at 1.
  unfold R.v6891, N.v6891.
  rewrite ?node_6889.
  rewrite ?node_6890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6892 (s : N.State) (i : N.Inputs) :
  R.v6892 (state s) (inputs i) = Zmod.unsigned (N.v6892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6892 s i)) at 1.
  unfold R.v6892, N.v6892.
  rewrite ?node_6888.
  rewrite ?node_6891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6893 (s : N.State) (i : N.Inputs) :
  R.v6893 (state s) (inputs i) = Zmod.unsigned (N.v6893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6893 s i)) at 1.
  unfold R.v6893, N.v6893.
  rewrite ?node_6885.
  rewrite ?node_6892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6894 (s : N.State) (i : N.Inputs) :
  R.v6894 (state s) (inputs i) = Zmod.unsigned (N.v6894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6894 s i)) at 1.
  unfold R.v6894, N.v6894.
  rewrite !state_r410_nr_5F410.
  rewrite !state_r411_nr_5F411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r410_nr_5F410 s)).
  rewrite ?(bits.mod_to_Z (N.r411_nr_5F411 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6895 (s : N.State) (i : N.Inputs) :
  R.v6895 (state s) (inputs i) = Zmod.unsigned (N.v6895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6895 s i)) at 1.
  unfold R.v6895, N.v6895.
  rewrite ?node_6894.
  rewrite !state_r412_nr_5F412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r412_nr_5F412 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6896 (s : N.State) (i : N.Inputs) :
  R.v6896 (state s) (inputs i) = Zmod.unsigned (N.v6896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6896 s i)) at 1.
  unfold R.v6896, N.v6896.
  rewrite ?node_6895.
  rewrite !state_r413_nr_5F413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r413_nr_5F413 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6897 (s : N.State) (i : N.Inputs) :
  R.v6897 (state s) (inputs i) = Zmod.unsigned (N.v6897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6897 s i)) at 1.
  unfold R.v6897, N.v6897.
  rewrite !state_r390_nr_5F390.
  rewrite !state_r391_nr_5F391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r390_nr_5F390 s)).
  rewrite ?(bits.mod_to_Z (N.r391_nr_5F391 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6898 (s : N.State) (i : N.Inputs) :
  R.v6898 (state s) (inputs i) = Zmod.unsigned (N.v6898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6898 s i)) at 1.
  unfold R.v6898, N.v6898.
  rewrite ?node_6802.
  rewrite !state_r392_nr_5F392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r392_nr_5F392 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6899 (s : N.State) (i : N.Inputs) :
  R.v6899 (state s) (inputs i) = Zmod.unsigned (N.v6899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6899 s i)) at 1.
  unfold R.v6899, N.v6899.
  rewrite ?node_6897.
  rewrite ?node_6898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6900 (s : N.State) (i : N.Inputs) :
  R.v6900 (state s) (inputs i) = Zmod.unsigned (N.v6900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6900 s i)) at 1.
  unfold R.v6900, N.v6900.
  rewrite ?node_6896.
  rewrite ?node_6899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6901 (s : N.State) (i : N.Inputs) :
  R.v6901 (state s) (inputs i) = Zmod.unsigned (N.v6901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6901 s i)) at 1.
  unfold R.v6901, N.v6901.
  rewrite ?node_6893.
  rewrite ?node_6900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6902 (s : N.State) (i : N.Inputs) :
  R.v6902 (state s) (inputs i) = Zmod.unsigned (N.v6902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6902 s i)) at 1.
  unfold R.v6902, N.v6902.
  rewrite ?node_6785.
  rewrite ?node_6792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6903 (s : N.State) (i : N.Inputs) :
  R.v6903 (state s) (inputs i) = Zmod.unsigned (N.v6903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6903 s i)) at 1.
  unfold R.v6903, N.v6903.
  rewrite ?node_6793.
  rewrite ?node_6800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6904 (s : N.State) (i : N.Inputs) :
  R.v6904 (state s) (inputs i) = Zmod.unsigned (N.v6904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6904 s i)) at 1.
  unfold R.v6904, N.v6904.
  rewrite ?node_6902.
  rewrite ?node_6903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6905 (s : N.State) (i : N.Inputs) :
  R.v6905 (state s) (inputs i) = Zmod.unsigned (N.v6905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6905 s i)) at 1.
  unfold R.v6905, N.v6905.
  rewrite ?node_6901.
  rewrite ?node_6904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6906 (s : N.State) (i : N.Inputs) :
  R.v6906 (state s) (inputs i) = Zmod.unsigned (N.v6906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6906 s i)) at 1.
  unfold R.v6906, N.v6906.
  rewrite !state_r414_nr_5F414.
  rewrite !state_r415_nr_5F415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r414_nr_5F414 s)).
  rewrite ?(bits.mod_to_Z (N.r415_nr_5F415 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6907 (s : N.State) (i : N.Inputs) :
  R.v6907 (state s) (inputs i) = Zmod.unsigned (N.v6907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6907 s i)) at 1.
  unfold R.v6907, N.v6907.
  rewrite ?node_6906.
  rewrite !state_r416_nr_5F416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r416_nr_5F416 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6908 (s : N.State) (i : N.Inputs) :
  R.v6908 (state s) (inputs i) = Zmod.unsigned (N.v6908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6908 s i)) at 1.
  unfold R.v6908, N.v6908.
  rewrite ?node_6907.
  rewrite !state_r417_nr_5F417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r417_nr_5F417 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6909 (s : N.State) (i : N.Inputs) :
  R.v6909 (state s) (inputs i) = Zmod.unsigned (N.v6909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6909 s i)) at 1.
  unfold R.v6909, N.v6909.
  rewrite !state_r394_nr_5F394.
  rewrite !state_r395_nr_5F395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r394_nr_5F394 s)).
  rewrite ?(bits.mod_to_Z (N.r395_nr_5F395 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6910 (s : N.State) (i : N.Inputs) :
  R.v6910 (state s) (inputs i) = Zmod.unsigned (N.v6910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6910 s i)) at 1.
  unfold R.v6910, N.v6910.
  rewrite ?node_6814.
  rewrite !state_r396_nr_5F396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r396_nr_5F396 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6911 (s : N.State) (i : N.Inputs) :
  R.v6911 (state s) (inputs i) = Zmod.unsigned (N.v6911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6911 s i)) at 1.
  unfold R.v6911, N.v6911.
  rewrite ?node_6909.
  rewrite ?node_6910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6912 (s : N.State) (i : N.Inputs) :
  R.v6912 (state s) (inputs i) = Zmod.unsigned (N.v6912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6912 s i)) at 1.
  unfold R.v6912, N.v6912.
  rewrite ?node_6908.
  rewrite ?node_6911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6913 (s : N.State) (i : N.Inputs) :
  R.v6913 (state s) (inputs i) = Zmod.unsigned (N.v6913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6913 s i)) at 1.
  unfold R.v6913, N.v6913.
  rewrite ?node_6780.
  rewrite !state_r381_nr_5F381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r381_nr_5F381 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6914 (s : N.State) (i : N.Inputs) :
  R.v6914 (state s) (inputs i) = Zmod.unsigned (N.v6914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6914 s i)) at 1.
  unfold R.v6914, N.v6914.
  rewrite ?node_6781.
  rewrite ?node_6784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6915 (s : N.State) (i : N.Inputs) :
  R.v6915 (state s) (inputs i) = Zmod.unsigned (N.v6915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6915 s i)) at 1.
  unfold R.v6915, N.v6915.
  rewrite ?node_6913.
  rewrite ?node_6914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6916 (s : N.State) (i : N.Inputs) :
  R.v6916 (state s) (inputs i) = Zmod.unsigned (N.v6916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6916 s i)) at 1.
  unfold R.v6916, N.v6916.
  rewrite ?node_6912.
  rewrite ?node_6915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6917 (s : N.State) (i : N.Inputs) :
  R.v6917 (state s) (inputs i) = Zmod.unsigned (N.v6917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6917 s i)) at 1.
  unfold R.v6917, N.v6917.
  rewrite ?node_6787.
  rewrite !state_r385_nr_5F385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r385_nr_5F385 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6918 (s : N.State) (i : N.Inputs) :
  R.v6918 (state s) (inputs i) = Zmod.unsigned (N.v6918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6918 s i)) at 1.
  unfold R.v6918, N.v6918.
  rewrite ?node_6788.
  rewrite ?node_6791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6919 (s : N.State) (i : N.Inputs) :
  R.v6919 (state s) (inputs i) = Zmod.unsigned (N.v6919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6919 s i)) at 1.
  unfold R.v6919, N.v6919.
  rewrite ?node_6917.
  rewrite ?node_6918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6920 (s : N.State) (i : N.Inputs) :
  R.v6920 (state s) (inputs i) = Zmod.unsigned (N.v6920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6920 s i)) at 1.
  unfold R.v6920, N.v6920.
  rewrite ?node_6916.
  rewrite ?node_6919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6921 (s : N.State) (i : N.Inputs) :
  R.v6921 (state s) (inputs i) = Zmod.unsigned (N.v6921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6921 s i)) at 1.
  unfold R.v6921, N.v6921.
  rewrite ?node_6795.
  rewrite !state_r389_nr_5F389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r389_nr_5F389 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6922 (s : N.State) (i : N.Inputs) :
  R.v6922 (state s) (inputs i) = Zmod.unsigned (N.v6922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6922 s i)) at 1.
  unfold R.v6922, N.v6922.
  rewrite ?node_6796.
  rewrite ?node_6799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6923 (s : N.State) (i : N.Inputs) :
  R.v6923 (state s) (inputs i) = Zmod.unsigned (N.v6923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6923 s i)) at 1.
  unfold R.v6923, N.v6923.
  rewrite ?node_6921.
  rewrite ?node_6922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6924 (s : N.State) (i : N.Inputs) :
  R.v6924 (state s) (inputs i) = Zmod.unsigned (N.v6924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6924 s i)) at 1.
  unfold R.v6924, N.v6924.
  rewrite ?node_6920.
  rewrite ?node_6923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6925 (s : N.State) (i : N.Inputs) :
  R.v6925 (state s) (inputs i) = Zmod.unsigned (N.v6925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6925 s i)) at 1.
  unfold R.v6925, N.v6925.
  rewrite ?node_6816.
  rewrite ?node_6819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6926 (s : N.State) (i : N.Inputs) :
  R.v6926 (state s) (inputs i) = Zmod.unsigned (N.v6926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6926 s i)) at 1.
  unfold R.v6926, N.v6926.
  rewrite ?node_6820.
  rewrite ?node_6823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6927 (s : N.State) (i : N.Inputs) :
  R.v6927 (state s) (inputs i) = Zmod.unsigned (N.v6927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6927 s i)) at 1.
  unfold R.v6927, N.v6927.
  rewrite ?node_6925.
  rewrite ?node_6926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6928 (s : N.State) (i : N.Inputs) :
  R.v6928 (state s) (inputs i) = Zmod.unsigned (N.v6928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6928 s i)) at 1.
  unfold R.v6928, N.v6928.
  rewrite ?node_6924.
  rewrite ?node_6927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6929 (s : N.State) (i : N.Inputs) :
  R.v6929 (state s) (inputs i) = Zmod.unsigned (N.v6929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6929 s i)) at 1.
  unfold R.v6929, N.v6929.
  rewrite ?node_6905.
  rewrite ?node_6928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6930 (s : N.State) (i : N.Inputs) :
  R.v6930 (state s) (inputs i) = Zmod.unsigned (N.v6930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6930 s i)) at 1.
  unfold R.v6930, N.v6930.
  rewrite ?node_6803.
  rewrite !state_r393_nr_5F393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r393_nr_5F393 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6931 (s : N.State) (i : N.Inputs) :
  R.v6931 (state s) (inputs i) = Zmod.unsigned (N.v6931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6931 s i)) at 1.
  unfold R.v6931, N.v6931.
  rewrite ?node_6804.
  rewrite ?node_6807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6932 (s : N.State) (i : N.Inputs) :
  R.v6932 (state s) (inputs i) = Zmod.unsigned (N.v6932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6932 s i)) at 1.
  unfold R.v6932, N.v6932.
  rewrite ?node_6930.
  rewrite ?node_6931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6933 (s : N.State) (i : N.Inputs) :
  R.v6933 (state s) (inputs i) = Zmod.unsigned (N.v6933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6933 s i)) at 1.
  unfold R.v6933, N.v6933.
  rewrite ?node_6815.
  rewrite !state_r397_nr_5F397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r397_nr_5F397 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6934 (s : N.State) (i : N.Inputs) :
  R.v6934 (state s) (inputs i) = Zmod.unsigned (N.v6934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6934 s i)) at 1.
  unfold R.v6934, N.v6934.
  rewrite ?node_6932.
  rewrite ?node_6933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6935 (s : N.State) (i : N.Inputs) :
  R.v6935 (state s) (inputs i) = Zmod.unsigned (N.v6935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6935 s i)) at 1.
  unfold R.v6935, N.v6935.
  rewrite ?node_6929.
  rewrite ?node_6934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6936 (s : N.State) (i : N.Inputs) :
  R.v6936 (state s) (inputs i) = Zmod.unsigned (N.v6936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6936 s i)) at 1.
  unfold R.v6936, N.v6936.
  rewrite ?node_6801.
  rewrite ?node_6808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6937 (s : N.State) (i : N.Inputs) :
  R.v6937 (state s) (inputs i) = Zmod.unsigned (N.v6937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6937 s i)) at 1.
  unfold R.v6937, N.v6937.
  rewrite ?node_6809.
  rewrite ?node_6812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6938 (s : N.State) (i : N.Inputs) :
  R.v6938 (state s) (inputs i) = Zmod.unsigned (N.v6938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6938 s i)) at 1.
  unfold R.v6938, N.v6938.
  rewrite ?node_6936.
  rewrite ?node_6937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6939 (s : N.State) (i : N.Inputs) :
  R.v6939 (state s) (inputs i) = Zmod.unsigned (N.v6939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6939 s i)) at 1.
  unfold R.v6939, N.v6939.
  rewrite ?node_6935.
  rewrite ?node_6938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6940 (s : N.State) (i : N.Inputs) :
  R.v6940 (state s) (inputs i) = Zmod.unsigned (N.v6940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6940 s i)) at 1.
  unfold R.v6940, N.v6940.
  rewrite ?node_6813.
  rewrite ?node_6832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6941 (s : N.State) (i : N.Inputs) :
  R.v6941 (state s) (inputs i) = Zmod.unsigned (N.v6941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6941 s i)) at 1.
  unfold R.v6941, N.v6941.
  rewrite ?node_6833.
  rewrite ?node_6840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6942 (s : N.State) (i : N.Inputs) :
  R.v6942 (state s) (inputs i) = Zmod.unsigned (N.v6942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6942 s i)) at 1.
  unfold R.v6942, N.v6942.
  rewrite ?node_6940.
  rewrite ?node_6941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6943 (s : N.State) (i : N.Inputs) :
  R.v6943 (state s) (inputs i) = Zmod.unsigned (N.v6943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6943 s i)) at 1.
  unfold R.v6943, N.v6943.
  rewrite ?node_6939.
  rewrite ?node_6942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6944 (s : N.State) (i : N.Inputs) :
  R.v6944 (state s) (inputs i) = Zmod.unsigned (N.v6944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6944 s i)) at 1.
  unfold R.v6944, N.v6944.
  rewrite ?node_6824.
  rewrite ?node_6827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6945 (s : N.State) (i : N.Inputs) :
  R.v6945 (state s) (inputs i) = Zmod.unsigned (N.v6945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6945 s i)) at 1.
  unfold R.v6945, N.v6945.
  rewrite ?node_6828.
  rewrite ?node_6831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6946 (s : N.State) (i : N.Inputs) :
  R.v6946 (state s) (inputs i) = Zmod.unsigned (N.v6946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6946 s i)) at 1.
  unfold R.v6946, N.v6946.
  rewrite ?node_6944.
  rewrite ?node_6945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6947 (s : N.State) (i : N.Inputs) :
  R.v6947 (state s) (inputs i) = Zmod.unsigned (N.v6947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6947 s i)) at 1.
  unfold R.v6947, N.v6947.
  rewrite ?node_6836.
  rewrite ?node_6839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6948 (s : N.State) (i : N.Inputs) :
  R.v6948 (state s) (inputs i) = Zmod.unsigned (N.v6948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6948 s i)) at 1.
  unfold R.v6948, N.v6948.
  rewrite ?node_6946.
  rewrite ?node_6947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6949 (s : N.State) (i : N.Inputs) :
  R.v6949 (state s) (inputs i) = Zmod.unsigned (N.v6949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6949 s i)) at 1.
  unfold R.v6949, N.v6949.
  rewrite ?node_6943.
  rewrite ?node_6948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6950 (s : N.State) (i : N.Inputs) :
  R.v6950 (state s) (inputs i) = Zmod.unsigned (N.v6950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6950 s i)) at 1.
  unfold R.v6950, N.v6950.
  rewrite ?node_6841.
  rewrite ?node_6844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6951 (s : N.State) (i : N.Inputs) :
  R.v6951 (state s) (inputs i) = Zmod.unsigned (N.v6951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6951 s i)) at 1.
  unfold R.v6951, N.v6951.
  rewrite ?node_6845.
  rewrite ?node_6848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6952 (s : N.State) (i : N.Inputs) :
  R.v6952 (state s) (inputs i) = Zmod.unsigned (N.v6952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6952 s i)) at 1.
  unfold R.v6952, N.v6952.
  rewrite ?node_6950.
  rewrite ?node_6951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6953 (s : N.State) (i : N.Inputs) :
  R.v6953 (state s) (inputs i) = Zmod.unsigned (N.v6953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6953 s i)) at 1.
  unfold R.v6953, N.v6953.
  rewrite ?node_6949.
  rewrite ?node_6952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6954 (s : N.State) (i : N.Inputs) :
  R.v6954 (state s) (inputs i) = Zmod.unsigned (N.v6954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6954 s i)) at 1.
  unfold R.v6954, N.v6954.
  rewrite ?node_6852.
  rewrite ?node_6853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6955 (s : N.State) (i : N.Inputs) :
  R.v6955 (state s) (inputs i) = Zmod.unsigned (N.v6955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6955 s i)) at 1.
  unfold R.v6955, N.v6955.
  rewrite ?node_6953.
  rewrite ?node_6954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6956 (s : N.State) (i : N.Inputs) :
  R.v6956 (state s) (inputs i) = Zmod.unsigned (N.v6956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6956 s i)) at 1.
  unfold R.v6956, N.v6956.
  rewrite ?node_6849.
  rewrite ?node_6854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6957 (s : N.State) (i : N.Inputs) :
  R.v6957 (state s) (inputs i) = Zmod.unsigned (N.v6957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6957 s i)) at 1.
  unfold R.v6957, N.v6957.
  rewrite ?node_6855.
  rewrite ?node_6858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6958 (s : N.State) (i : N.Inputs) :
  R.v6958 (state s) (inputs i) = Zmod.unsigned (N.v6958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6958 s i)) at 1.
  unfold R.v6958, N.v6958.
  rewrite ?node_6956.
  rewrite ?node_6957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6959 (s : N.State) (i : N.Inputs) :
  R.v6959 (state s) (inputs i) = Zmod.unsigned (N.v6959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6959 s i)) at 1.
  unfold R.v6959, N.v6959.
  rewrite ?node_6955.
  rewrite ?node_6958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6960 (s : N.State) (i : N.Inputs) :
  R.v6960 (state s) (inputs i) = Zmod.unsigned (N.v6960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6960 s i)) at 1.
  unfold R.v6960, N.v6960.
  rewrite ?node_6859.
  rewrite ?node_6860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6961 (s : N.State) (i : N.Inputs) :
  R.v6961 (state s) (inputs i) = Zmod.unsigned (N.v6961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6961 s i)) at 1.
  unfold R.v6961, N.v6961.
  rewrite ?node_6861.
  rewrite ?node_6864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6962 (s : N.State) (i : N.Inputs) :
  R.v6962 (state s) (inputs i) = Zmod.unsigned (N.v6962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6962 s i)) at 1.
  unfold R.v6962, N.v6962.
  rewrite ?node_6960.
  rewrite ?node_6961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6963 (s : N.State) (i : N.Inputs) :
  R.v6963 (state s) (inputs i) = Zmod.unsigned (N.v6963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6963 s i)) at 1.
  unfold R.v6963, N.v6963.
  rewrite ?node_6959.
  rewrite ?node_6962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6964 (s : N.State) (i : N.Inputs) :
  R.v6964 (state s) (inputs i) = Zmod.unsigned (N.v6964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6964 s i)) at 1.
  unfold R.v6964, N.v6964.
  rewrite ?node_6963.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2347_nr_5F2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2347_nr_5F2378 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6965 (s : N.State) (i : N.Inputs) :
  R.v6965 (state s) (inputs i) = Zmod.unsigned (N.v6965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6965 s i)) at 1.
  unfold R.v6965, N.v6965.
  rewrite ?node_6865.
  rewrite ?node_6866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6966 (s : N.State) (i : N.Inputs) :
  R.v6966 (state s) (inputs i) = Zmod.unsigned (N.v6966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6966 s i)) at 1.
  unfold R.v6966, N.v6966.
  rewrite ?node_6965.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2348_nr_5F2379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2348_nr_5F2379 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6967 (s : N.State) (i : N.Inputs) :
  R.v6967 (state s) (inputs i) = Zmod.unsigned (N.v6967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6967 s i)) at 1.
  unfold R.v6967, N.v6967.
  rewrite !state_r418_nr_5F418.
  rewrite !state_r419_nr_5F419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r418_nr_5F418 s)).
  rewrite ?(bits.mod_to_Z (N.r419_nr_5F419 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6968 (s : N.State) (i : N.Inputs) :
  R.v6968 (state s) (inputs i) = Zmod.unsigned (N.v6968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6968 s i)) at 1.
  unfold R.v6968, N.v6968.
  rewrite ?node_6967.
  rewrite !state_r420_nr_5F420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r420_nr_5F420 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6969 (s : N.State) (i : N.Inputs) :
  R.v6969 (state s) (inputs i) = Zmod.unsigned (N.v6969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6969 s i)) at 1.
  unfold R.v6969, N.v6969.
  rewrite ?node_6968.
  rewrite !state_r421_nr_5F421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r421_nr_5F421 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6970 (s : N.State) (i : N.Inputs) :
  R.v6970 (state s) (inputs i) = Zmod.unsigned (N.v6970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6970 s i)) at 1.
  unfold R.v6970, N.v6970.
  rewrite !state_r398_nr_5F398.
  rewrite !state_r399_nr_5F399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r398_nr_5F398 s)).
  rewrite ?(bits.mod_to_Z (N.r399_nr_5F399 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6971 (s : N.State) (i : N.Inputs) :
  R.v6971 (state s) (inputs i) = Zmod.unsigned (N.v6971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6971 s i)) at 1.
  unfold R.v6971, N.v6971.
  rewrite ?node_6871.
  rewrite !state_r400_nr_5F400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r400_nr_5F400 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6972 (s : N.State) (i : N.Inputs) :
  R.v6972 (state s) (inputs i) = Zmod.unsigned (N.v6972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6972 s i)) at 1.
  unfold R.v6972, N.v6972.
  rewrite ?node_6970.
  rewrite ?node_6971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6973 (s : N.State) (i : N.Inputs) :
  R.v6973 (state s) (inputs i) = Zmod.unsigned (N.v6973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6973 s i)) at 1.
  unfold R.v6973, N.v6973.
  rewrite ?node_6969.
  rewrite ?node_6972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6974 (s : N.State) (i : N.Inputs) :
  R.v6974 (state s) (inputs i) = Zmod.unsigned (N.v6974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6974 s i)) at 1.
  unfold R.v6974, N.v6974.
  rewrite !state_r422_nr_5F422.
  rewrite !state_r423_nr_5F423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r422_nr_5F422 s)).
  rewrite ?(bits.mod_to_Z (N.r423_nr_5F423 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6975 (s : N.State) (i : N.Inputs) :
  R.v6975 (state s) (inputs i) = Zmod.unsigned (N.v6975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6975 s i)) at 1.
  unfold R.v6975, N.v6975.
  rewrite ?node_6974.
  rewrite !state_r424_nr_5F424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r424_nr_5F424 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6976 (s : N.State) (i : N.Inputs) :
  R.v6976 (state s) (inputs i) = Zmod.unsigned (N.v6976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6976 s i)) at 1.
  unfold R.v6976, N.v6976.
  rewrite ?node_6975.
  rewrite !state_r425_nr_5F425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r425_nr_5F425 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6977 (s : N.State) (i : N.Inputs) :
  R.v6977 (state s) (inputs i) = Zmod.unsigned (N.v6977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6977 s i)) at 1.
  unfold R.v6977, N.v6977.
  rewrite !state_r402_nr_5F402.
  rewrite !state_r403_nr_5F403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r402_nr_5F402 s)).
  rewrite ?(bits.mod_to_Z (N.r403_nr_5F403 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6978 (s : N.State) (i : N.Inputs) :
  R.v6978 (state s) (inputs i) = Zmod.unsigned (N.v6978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6978 s i)) at 1.
  unfold R.v6978, N.v6978.
  rewrite ?node_6878.
  rewrite !state_r404_nr_5F404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r404_nr_5F404 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6979 (s : N.State) (i : N.Inputs) :
  R.v6979 (state s) (inputs i) = Zmod.unsigned (N.v6979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6979 s i)) at 1.
  unfold R.v6979, N.v6979.
  rewrite ?node_6977.
  rewrite ?node_6978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6980 (s : N.State) (i : N.Inputs) :
  R.v6980 (state s) (inputs i) = Zmod.unsigned (N.v6980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6980 s i)) at 1.
  unfold R.v6980, N.v6980.
  rewrite ?node_6976.
  rewrite ?node_6979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6981 (s : N.State) (i : N.Inputs) :
  R.v6981 (state s) (inputs i) = Zmod.unsigned (N.v6981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6981 s i)) at 1.
  unfold R.v6981, N.v6981.
  rewrite ?node_6973.
  rewrite ?node_6980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6982 (s : N.State) (i : N.Inputs) :
  R.v6982 (state s) (inputs i) = Zmod.unsigned (N.v6982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6982 s i)) at 1.
  unfold R.v6982, N.v6982.
  rewrite !state_r426_nr_5F426.
  rewrite !state_r427_nr_5F427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r426_nr_5F426 s)).
  rewrite ?(bits.mod_to_Z (N.r427_nr_5F427 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6983 (s : N.State) (i : N.Inputs) :
  R.v6983 (state s) (inputs i) = Zmod.unsigned (N.v6983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6983 s i)) at 1.
  unfold R.v6983, N.v6983.
  rewrite ?node_6982.
  rewrite !state_r428_nr_5F428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r428_nr_5F428 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6984 (s : N.State) (i : N.Inputs) :
  R.v6984 (state s) (inputs i) = Zmod.unsigned (N.v6984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6984 s i)) at 1.
  unfold R.v6984, N.v6984.
  rewrite ?node_6983.
  rewrite !state_r429_nr_5F429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r429_nr_5F429 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6985 (s : N.State) (i : N.Inputs) :
  R.v6985 (state s) (inputs i) = Zmod.unsigned (N.v6985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6985 s i)) at 1.
  unfold R.v6985, N.v6985.
  rewrite !state_r406_nr_5F406.
  rewrite !state_r407_nr_5F407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r406_nr_5F406 s)).
  rewrite ?(bits.mod_to_Z (N.r407_nr_5F407 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6986 (s : N.State) (i : N.Inputs) :
  R.v6986 (state s) (inputs i) = Zmod.unsigned (N.v6986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6986 s i)) at 1.
  unfold R.v6986, N.v6986.
  rewrite ?node_6886.
  rewrite !state_r408_nr_5F408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r408_nr_5F408 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6987 (s : N.State) (i : N.Inputs) :
  R.v6987 (state s) (inputs i) = Zmod.unsigned (N.v6987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6987 s i)) at 1.
  unfold R.v6987, N.v6987.
  rewrite ?node_6985.
  rewrite ?node_6986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6988 (s : N.State) (i : N.Inputs) :
  R.v6988 (state s) (inputs i) = Zmod.unsigned (N.v6988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6988 s i)) at 1.
  unfold R.v6988, N.v6988.
  rewrite ?node_6984.
  rewrite ?node_6987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6989 (s : N.State) (i : N.Inputs) :
  R.v6989 (state s) (inputs i) = Zmod.unsigned (N.v6989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6989 s i)) at 1.
  unfold R.v6989, N.v6989.
  rewrite ?node_6981.
  rewrite ?node_6988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6990 (s : N.State) (i : N.Inputs) :
  R.v6990 (state s) (inputs i) = Zmod.unsigned (N.v6990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6990 s i)) at 1.
  unfold R.v6990, N.v6990.
  rewrite !state_r430_nr_5F430.
  rewrite !state_r431_nr_5F431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r430_nr_5F430 s)).
  rewrite ?(bits.mod_to_Z (N.r431_nr_5F431 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6991 (s : N.State) (i : N.Inputs) :
  R.v6991 (state s) (inputs i) = Zmod.unsigned (N.v6991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6991 s i)) at 1.
  unfold R.v6991, N.v6991.
  rewrite ?node_6990.
  rewrite !state_r432_nr_5F432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r432_nr_5F432 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6992 (s : N.State) (i : N.Inputs) :
  R.v6992 (state s) (inputs i) = Zmod.unsigned (N.v6992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6992 s i)) at 1.
  unfold R.v6992, N.v6992.
  rewrite ?node_6991.
  rewrite !state_r433_nr_5F433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r433_nr_5F433 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6993 (s : N.State) (i : N.Inputs) :
  R.v6993 (state s) (inputs i) = Zmod.unsigned (N.v6993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6993 s i)) at 1.
  unfold R.v6993, N.v6993.
  rewrite !state_r410_nr_5F410.
  rewrite !state_r411_nr_5F411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r410_nr_5F410 s)).
  rewrite ?(bits.mod_to_Z (N.r411_nr_5F411 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6994 (s : N.State) (i : N.Inputs) :
  R.v6994 (state s) (inputs i) = Zmod.unsigned (N.v6994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6994 s i)) at 1.
  unfold R.v6994, N.v6994.
  rewrite ?node_6894.
  rewrite !state_r412_nr_5F412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r412_nr_5F412 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6995 (s : N.State) (i : N.Inputs) :
  R.v6995 (state s) (inputs i) = Zmod.unsigned (N.v6995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6995 s i)) at 1.
  unfold R.v6995, N.v6995.
  rewrite ?node_6993.
  rewrite ?node_6994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6996 (s : N.State) (i : N.Inputs) :
  R.v6996 (state s) (inputs i) = Zmod.unsigned (N.v6996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6996 s i)) at 1.
  unfold R.v6996, N.v6996.
  rewrite ?node_6992.
  rewrite ?node_6995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6997 (s : N.State) (i : N.Inputs) :
  R.v6997 (state s) (inputs i) = Zmod.unsigned (N.v6997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6997 s i)) at 1.
  unfold R.v6997, N.v6997.
  rewrite ?node_6989.
  rewrite ?node_6996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6998 (s : N.State) (i : N.Inputs) :
  R.v6998 (state s) (inputs i) = Zmod.unsigned (N.v6998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6998 s i)) at 1.
  unfold R.v6998, N.v6998.
  rewrite ?node_6877.
  rewrite ?node_6884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6999 (s : N.State) (i : N.Inputs) :
  R.v6999 (state s) (inputs i) = Zmod.unsigned (N.v6999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6999 s i)) at 1.
  unfold R.v6999, N.v6999.
  rewrite ?node_6885.
  rewrite ?node_6892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
