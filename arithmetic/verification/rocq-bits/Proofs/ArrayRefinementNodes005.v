(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes004.
Lemma node_5000 (s : N.State) (i : N.Inputs) :
  R.v5000 (state s) (inputs i) = Zmod.unsigned (N.v5000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5000 s i)) at 1.
  unfold R.v5000, N.v5000.
  unfold R.v3021, N.v3021.
  rewrite ?node_4999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5001 (s : N.State) (i : N.Inputs) :
  R.v5001 (state s) (inputs i) = Zmod.unsigned (N.v5001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5001 s i)) at 1.
  unfold R.v5001, N.v5001.
  rewrite ?node_5000.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2230_nr_5F2255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2230_nr_5F2255 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5002 (s : N.State) (i : N.Inputs) :
  R.v5002 (state s) (inputs i) = Zmod.unsigned (N.v5002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5002 s i)) at 1.
  unfold R.v5002, N.v5002.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5003 (s : N.State) (i : N.Inputs) :
  R.v5003 (state s) (inputs i) = Zmod.unsigned (N.v5003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5003 s i)) at 1.
  unfold R.v5003, N.v5003.
  rewrite ?node_5002.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2231_nr_5F2256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2231_nr_5F2256 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5004 (s : N.State) (i : N.Inputs) :
  R.v5004 (state s) (inputs i) = Zmod.unsigned (N.v5004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5004 s i)) at 1.
  unfold R.v5004, N.v5004.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5005 (s : N.State) (i : N.Inputs) :
  R.v5005 (state s) (inputs i) = Zmod.unsigned (N.v5005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5005 s i)) at 1.
  unfold R.v5005, N.v5005.
  rewrite ?node_5004.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2232_nr_5F2257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2232_nr_5F2257 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5006 (s : N.State) (i : N.Inputs) :
  R.v5006 (state s) (inputs i) = Zmod.unsigned (N.v5006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5006 s i)) at 1.
  unfold R.v5006, N.v5006.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5007 (s : N.State) (i : N.Inputs) :
  R.v5007 (state s) (inputs i) = Zmod.unsigned (N.v5007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5007 s i)) at 1.
  unfold R.v5007, N.v5007.
  rewrite ?node_5006.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2233_nr_5F2258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2233_nr_5F2258 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5008 (s : N.State) (i : N.Inputs) :
  R.v5008 (state s) (inputs i) = Zmod.unsigned (N.v5008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5008 s i)) at 1.
  unfold R.v5008, N.v5008.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5009 (s : N.State) (i : N.Inputs) :
  R.v5009 (state s) (inputs i) = Zmod.unsigned (N.v5009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5009 s i)) at 1.
  unfold R.v5009, N.v5009.
  rewrite ?node_5008.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2234_nr_5F2259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2234_nr_5F2259 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5010 (s : N.State) (i : N.Inputs) :
  R.v5010 (state s) (inputs i) = Zmod.unsigned (N.v5010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5010 s i)) at 1.
  unfold R.v5010, N.v5010.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5011 (s : N.State) (i : N.Inputs) :
  R.v5011 (state s) (inputs i) = Zmod.unsigned (N.v5011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5011 s i)) at 1.
  unfold R.v5011, N.v5011.
  rewrite ?node_5010.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2235_nr_5F2260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2235_nr_5F2260 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5012 (s : N.State) (i : N.Inputs) :
  R.v5012 (state s) (inputs i) = Zmod.unsigned (N.v5012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5012 s i)) at 1.
  unfold R.v5012, N.v5012.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5013 (s : N.State) (i : N.Inputs) :
  R.v5013 (state s) (inputs i) = Zmod.unsigned (N.v5013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5013 s i)) at 1.
  unfold R.v5013, N.v5013.
  rewrite ?node_5012.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2236_nr_5F2261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2236_nr_5F2261 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5014 (s : N.State) (i : N.Inputs) :
  R.v5014 (state s) (inputs i) = Zmod.unsigned (N.v5014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5014 s i)) at 1.
  unfold R.v5014, N.v5014.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5015 (s : N.State) (i : N.Inputs) :
  R.v5015 (state s) (inputs i) = Zmod.unsigned (N.v5015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5015 s i)) at 1.
  unfold R.v5015, N.v5015.
  rewrite ?node_5014.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2237_nr_5F2263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2237_nr_5F2263 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5016 (s : N.State) (i : N.Inputs) :
  R.v5016 (state s) (inputs i) = Zmod.unsigned (N.v5016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5016 s i)) at 1.
  unfold R.v5016, N.v5016.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5017 (s : N.State) (i : N.Inputs) :
  R.v5017 (state s) (inputs i) = Zmod.unsigned (N.v5017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5017 s i)) at 1.
  unfold R.v5017, N.v5017.
  rewrite ?node_5016.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2238_nr_5F2264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2238_nr_5F2264 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5018 (s : N.State) (i : N.Inputs) :
  R.v5018 (state s) (inputs i) = Zmod.unsigned (N.v5018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5018 s i)) at 1.
  unfold R.v5018, N.v5018.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5019 (s : N.State) (i : N.Inputs) :
  R.v5019 (state s) (inputs i) = Zmod.unsigned (N.v5019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5019 s i)) at 1.
  unfold R.v5019, N.v5019.
  rewrite ?node_5018.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2239_nr_5F2265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2239_nr_5F2265 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5020 (s : N.State) (i : N.Inputs) :
  R.v5020 (state s) (inputs i) = Zmod.unsigned (N.v5020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5020 s i)) at 1.
  unfold R.v5020, N.v5020.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5021 (s : N.State) (i : N.Inputs) :
  R.v5021 (state s) (inputs i) = Zmod.unsigned (N.v5021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5021 s i)) at 1.
  unfold R.v5021, N.v5021.
  rewrite ?node_5020.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2240_nr_5F2266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2240_nr_5F2266 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5022 (s : N.State) (i : N.Inputs) :
  R.v5022 (state s) (inputs i) = Zmod.unsigned (N.v5022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5022 s i)) at 1.
  unfold R.v5022, N.v5022.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5023 (s : N.State) (i : N.Inputs) :
  R.v5023 (state s) (inputs i) = Zmod.unsigned (N.v5023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5023 s i)) at 1.
  unfold R.v5023, N.v5023.
  rewrite ?node_5022.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2241_nr_5F2267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2241_nr_5F2267 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5024 (s : N.State) (i : N.Inputs) :
  R.v5024 (state s) (inputs i) = Zmod.unsigned (N.v5024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5024 s i)) at 1.
  unfold R.v5024, N.v5024.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5025 (s : N.State) (i : N.Inputs) :
  R.v5025 (state s) (inputs i) = Zmod.unsigned (N.v5025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5025 s i)) at 1.
  unfold R.v5025, N.v5025.
  rewrite ?node_5024.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2242_nr_5F2268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2242_nr_5F2268 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5026 (s : N.State) (i : N.Inputs) :
  R.v5026 (state s) (inputs i) = Zmod.unsigned (N.v5026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5026 s i)) at 1.
  unfold R.v5026, N.v5026.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5027 (s : N.State) (i : N.Inputs) :
  R.v5027 (state s) (inputs i) = Zmod.unsigned (N.v5027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5027 s i)) at 1.
  unfold R.v5027, N.v5027.
  unfold R.v3021, N.v3021.
  rewrite ?node_5026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5028 (s : N.State) (i : N.Inputs) :
  R.v5028 (state s) (inputs i) = Zmod.unsigned (N.v5028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5028 s i)) at 1.
  unfold R.v5028, N.v5028.
  rewrite ?node_5027.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2243_nr_5F2269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2243_nr_5F2269 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5029 (s : N.State) (i : N.Inputs) :
  R.v5029 (state s) (inputs i) = Zmod.unsigned (N.v5029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5029 s i)) at 1.
  unfold R.v5029, N.v5029.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5030 (s : N.State) (i : N.Inputs) :
  R.v5030 (state s) (inputs i) = Zmod.unsigned (N.v5030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5030 s i)) at 1.
  unfold R.v5030, N.v5030.
  rewrite ?node_5029.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2244_nr_5F2270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2244_nr_5F2270 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5031 (s : N.State) (i : N.Inputs) :
  R.v5031 (state s) (inputs i) = Zmod.unsigned (N.v5031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5031 s i)) at 1.
  unfold R.v5031, N.v5031.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5032 (s : N.State) (i : N.Inputs) :
  R.v5032 (state s) (inputs i) = Zmod.unsigned (N.v5032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5032 s i)) at 1.
  unfold R.v5032, N.v5032.
  rewrite ?node_5031.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2245_nr_5F2271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2245_nr_5F2271 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5033 (s : N.State) (i : N.Inputs) :
  R.v5033 (state s) (inputs i) = Zmod.unsigned (N.v5033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5033 s i)) at 1.
  unfold R.v5033, N.v5033.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5034 (s : N.State) (i : N.Inputs) :
  R.v5034 (state s) (inputs i) = Zmod.unsigned (N.v5034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5034 s i)) at 1.
  unfold R.v5034, N.v5034.
  rewrite ?node_5033.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2246_nr_5F2272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2246_nr_5F2272 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5035 (s : N.State) (i : N.Inputs) :
  R.v5035 (state s) (inputs i) = Zmod.unsigned (N.v5035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5035 s i)) at 1.
  unfold R.v5035, N.v5035.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5036 (s : N.State) (i : N.Inputs) :
  R.v5036 (state s) (inputs i) = Zmod.unsigned (N.v5036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5036 s i)) at 1.
  unfold R.v5036, N.v5036.
  rewrite ?node_5035.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2247_nr_5F2273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2247_nr_5F2273 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5037 (s : N.State) (i : N.Inputs) :
  R.v5037 (state s) (inputs i) = Zmod.unsigned (N.v5037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5037 s i)) at 1.
  unfold R.v5037, N.v5037.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5038 (s : N.State) (i : N.Inputs) :
  R.v5038 (state s) (inputs i) = Zmod.unsigned (N.v5038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5038 s i)) at 1.
  unfold R.v5038, N.v5038.
  rewrite ?node_5037.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2248_nr_5F2274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2248_nr_5F2274 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5039 (s : N.State) (i : N.Inputs) :
  R.v5039 (state s) (inputs i) = Zmod.unsigned (N.v5039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5039 s i)) at 1.
  unfold R.v5039, N.v5039.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5040 (s : N.State) (i : N.Inputs) :
  R.v5040 (state s) (inputs i) = Zmod.unsigned (N.v5040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5040 s i)) at 1.
  unfold R.v5040, N.v5040.
  rewrite ?node_5039.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2249_nr_5F2276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2249_nr_5F2276 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5041 (s : N.State) (i : N.Inputs) :
  R.v5041 (state s) (inputs i) = Zmod.unsigned (N.v5041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5041 s i)) at 1.
  unfold R.v5041, N.v5041.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5042 (s : N.State) (i : N.Inputs) :
  R.v5042 (state s) (inputs i) = Zmod.unsigned (N.v5042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5042 s i)) at 1.
  unfold R.v5042, N.v5042.
  rewrite ?node_5041.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2250_nr_5F2277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2250_nr_5F2277 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5043 (s : N.State) (i : N.Inputs) :
  R.v5043 (state s) (inputs i) = Zmod.unsigned (N.v5043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5043 s i)) at 1.
  unfold R.v5043, N.v5043.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5044 (s : N.State) (i : N.Inputs) :
  R.v5044 (state s) (inputs i) = Zmod.unsigned (N.v5044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5044 s i)) at 1.
  unfold R.v5044, N.v5044.
  rewrite ?node_5043.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2251_nr_5F2278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2251_nr_5F2278 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5045 (s : N.State) (i : N.Inputs) :
  R.v5045 (state s) (inputs i) = Zmod.unsigned (N.v5045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5045 s i)) at 1.
  unfold R.v5045, N.v5045.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5046 (s : N.State) (i : N.Inputs) :
  R.v5046 (state s) (inputs i) = Zmod.unsigned (N.v5046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5046 s i)) at 1.
  unfold R.v5046, N.v5046.
  rewrite ?node_5045.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2252_nr_5F2279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2252_nr_5F2279 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5047 (s : N.State) (i : N.Inputs) :
  R.v5047 (state s) (inputs i) = Zmod.unsigned (N.v5047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5047 s i)) at 1.
  unfold R.v5047, N.v5047.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5048 (s : N.State) (i : N.Inputs) :
  R.v5048 (state s) (inputs i) = Zmod.unsigned (N.v5048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5048 s i)) at 1.
  unfold R.v5048, N.v5048.
  rewrite ?node_5047.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2253_nr_5F2280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2253_nr_5F2280 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5049 (s : N.State) (i : N.Inputs) :
  R.v5049 (state s) (inputs i) = Zmod.unsigned (N.v5049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5049 s i)) at 1.
  unfold R.v5049, N.v5049.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5050 (s : N.State) (i : N.Inputs) :
  R.v5050 (state s) (inputs i) = Zmod.unsigned (N.v5050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5050 s i)) at 1.
  unfold R.v5050, N.v5050.
  unfold R.v3021, N.v3021.
  rewrite ?node_5049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5051 (s : N.State) (i : N.Inputs) :
  R.v5051 (state s) (inputs i) = Zmod.unsigned (N.v5051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5051 s i)) at 1.
  unfold R.v5051, N.v5051.
  rewrite ?node_5050.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2254_nr_5F2281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2254_nr_5F2281 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5052 (s : N.State) (i : N.Inputs) :
  R.v5052 (state s) (inputs i) = Zmod.unsigned (N.v5052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5052 s i)) at 1.
  unfold R.v5052, N.v5052.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5053 (s : N.State) (i : N.Inputs) :
  R.v5053 (state s) (inputs i) = Zmod.unsigned (N.v5053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5053 s i)) at 1.
  unfold R.v5053, N.v5053.
  rewrite ?node_5052.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2255_nr_5F2282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2255_nr_5F2282 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5054 (s : N.State) (i : N.Inputs) :
  R.v5054 (state s) (inputs i) = Zmod.unsigned (N.v5054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5054 s i)) at 1.
  unfold R.v5054, N.v5054.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5055 (s : N.State) (i : N.Inputs) :
  R.v5055 (state s) (inputs i) = Zmod.unsigned (N.v5055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5055 s i)) at 1.
  unfold R.v5055, N.v5055.
  rewrite ?node_5054.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2256_nr_5F2283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2256_nr_5F2283 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5056 (s : N.State) (i : N.Inputs) :
  R.v5056 (state s) (inputs i) = Zmod.unsigned (N.v5056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5056 s i)) at 1.
  unfold R.v5056, N.v5056.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5057 (s : N.State) (i : N.Inputs) :
  R.v5057 (state s) (inputs i) = Zmod.unsigned (N.v5057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5057 s i)) at 1.
  unfold R.v5057, N.v5057.
  rewrite ?node_5056.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2257_nr_5F2284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2257_nr_5F2284 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5058 (s : N.State) (i : N.Inputs) :
  R.v5058 (state s) (inputs i) = Zmod.unsigned (N.v5058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5058 s i)) at 1.
  unfold R.v5058, N.v5058.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5059 (s : N.State) (i : N.Inputs) :
  R.v5059 (state s) (inputs i) = Zmod.unsigned (N.v5059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5059 s i)) at 1.
  unfold R.v5059, N.v5059.
  rewrite ?node_5058.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2258_nr_5F2285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2258_nr_5F2285 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5060 (s : N.State) (i : N.Inputs) :
  R.v5060 (state s) (inputs i) = Zmod.unsigned (N.v5060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5060 s i)) at 1.
  unfold R.v5060, N.v5060.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5061 (s : N.State) (i : N.Inputs) :
  R.v5061 (state s) (inputs i) = Zmod.unsigned (N.v5061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5061 s i)) at 1.
  unfold R.v5061, N.v5061.
  rewrite ?node_5060.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2259_nr_5F2287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2259_nr_5F2287 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5062 (s : N.State) (i : N.Inputs) :
  R.v5062 (state s) (inputs i) = Zmod.unsigned (N.v5062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5062 s i)) at 1.
  unfold R.v5062, N.v5062.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5063 (s : N.State) (i : N.Inputs) :
  R.v5063 (state s) (inputs i) = Zmod.unsigned (N.v5063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5063 s i)) at 1.
  unfold R.v5063, N.v5063.
  rewrite ?node_5062.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2260_nr_5F2288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2260_nr_5F2288 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5064 (s : N.State) (i : N.Inputs) :
  R.v5064 (state s) (inputs i) = Zmod.unsigned (N.v5064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5064 s i)) at 1.
  unfold R.v5064, N.v5064.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5065 (s : N.State) (i : N.Inputs) :
  R.v5065 (state s) (inputs i) = Zmod.unsigned (N.v5065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5065 s i)) at 1.
  unfold R.v5065, N.v5065.
  rewrite ?node_5064.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2261_nr_5F2289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2261_nr_5F2289 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5066 (s : N.State) (i : N.Inputs) :
  R.v5066 (state s) (inputs i) = Zmod.unsigned (N.v5066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5066 s i)) at 1.
  unfold R.v5066, N.v5066.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5067 (s : N.State) (i : N.Inputs) :
  R.v5067 (state s) (inputs i) = Zmod.unsigned (N.v5067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5067 s i)) at 1.
  unfold R.v5067, N.v5067.
  rewrite ?node_5066.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2262_nr_5F2290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2262_nr_5F2290 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5068 (s : N.State) (i : N.Inputs) :
  R.v5068 (state s) (inputs i) = Zmod.unsigned (N.v5068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5068 s i)) at 1.
  unfold R.v5068, N.v5068.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5069 (s : N.State) (i : N.Inputs) :
  R.v5069 (state s) (inputs i) = Zmod.unsigned (N.v5069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5069 s i)) at 1.
  unfold R.v5069, N.v5069.
  unfold R.v3021, N.v3021.
  rewrite ?node_5068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5070 (s : N.State) (i : N.Inputs) :
  R.v5070 (state s) (inputs i) = Zmod.unsigned (N.v5070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5070 s i)) at 1.
  unfold R.v5070, N.v5070.
  rewrite ?node_5069.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2263_nr_5F2291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2263_nr_5F2291 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5071 (s : N.State) (i : N.Inputs) :
  R.v5071 (state s) (inputs i) = Zmod.unsigned (N.v5071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5071 s i)) at 1.
  unfold R.v5071, N.v5071.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5072 (s : N.State) (i : N.Inputs) :
  R.v5072 (state s) (inputs i) = Zmod.unsigned (N.v5072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5072 s i)) at 1.
  unfold R.v5072, N.v5072.
  rewrite ?node_5071.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2264_nr_5F2292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2264_nr_5F2292 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5073 (s : N.State) (i : N.Inputs) :
  R.v5073 (state s) (inputs i) = Zmod.unsigned (N.v5073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5073 s i)) at 1.
  unfold R.v5073, N.v5073.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5074 (s : N.State) (i : N.Inputs) :
  R.v5074 (state s) (inputs i) = Zmod.unsigned (N.v5074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5074 s i)) at 1.
  unfold R.v5074, N.v5074.
  rewrite ?node_5073.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2265_nr_5F2293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2265_nr_5F2293 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5075 (s : N.State) (i : N.Inputs) :
  R.v5075 (state s) (inputs i) = Zmod.unsigned (N.v5075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5075 s i)) at 1.
  unfold R.v5075, N.v5075.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5076 (s : N.State) (i : N.Inputs) :
  R.v5076 (state s) (inputs i) = Zmod.unsigned (N.v5076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5076 s i)) at 1.
  unfold R.v5076, N.v5076.
  rewrite ?node_5075.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2266_nr_5F2294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2266_nr_5F2294 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5077 (s : N.State) (i : N.Inputs) :
  R.v5077 (state s) (inputs i) = Zmod.unsigned (N.v5077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5077 s i)) at 1.
  unfold R.v5077, N.v5077.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5078 (s : N.State) (i : N.Inputs) :
  R.v5078 (state s) (inputs i) = Zmod.unsigned (N.v5078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5078 s i)) at 1.
  unfold R.v5078, N.v5078.
  rewrite ?node_5077.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2267_nr_5F2296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2267_nr_5F2296 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5079 (s : N.State) (i : N.Inputs) :
  R.v5079 (state s) (inputs i) = Zmod.unsigned (N.v5079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5079 s i)) at 1.
  unfold R.v5079, N.v5079.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5080 (s : N.State) (i : N.Inputs) :
  R.v5080 (state s) (inputs i) = Zmod.unsigned (N.v5080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5080 s i)) at 1.
  unfold R.v5080, N.v5080.
  rewrite ?node_5079.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2268_nr_5F2297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2268_nr_5F2297 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5081 (s : N.State) (i : N.Inputs) :
  R.v5081 (state s) (inputs i) = Zmod.unsigned (N.v5081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5081 s i)) at 1.
  unfold R.v5081, N.v5081.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5082 (s : N.State) (i : N.Inputs) :
  R.v5082 (state s) (inputs i) = Zmod.unsigned (N.v5082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5082 s i)) at 1.
  unfold R.v5082, N.v5082.
  rewrite ?node_5081.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2269_nr_5F2298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2269_nr_5F2298 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5083 (s : N.State) (i : N.Inputs) :
  R.v5083 (state s) (inputs i) = Zmod.unsigned (N.v5083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5083 s i)) at 1.
  unfold R.v5083, N.v5083.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5084 (s : N.State) (i : N.Inputs) :
  R.v5084 (state s) (inputs i) = Zmod.unsigned (N.v5084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5084 s i)) at 1.
  unfold R.v5084, N.v5084.
  unfold R.v3021, N.v3021.
  rewrite ?node_5083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5085 (s : N.State) (i : N.Inputs) :
  R.v5085 (state s) (inputs i) = Zmod.unsigned (N.v5085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5085 s i)) at 1.
  unfold R.v5085, N.v5085.
  rewrite ?node_5084.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2270_nr_5F2299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2270_nr_5F2299 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5086 (s : N.State) (i : N.Inputs) :
  R.v5086 (state s) (inputs i) = Zmod.unsigned (N.v5086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5086 s i)) at 1.
  unfold R.v5086, N.v5086.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5087 (s : N.State) (i : N.Inputs) :
  R.v5087 (state s) (inputs i) = Zmod.unsigned (N.v5087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5087 s i)) at 1.
  unfold R.v5087, N.v5087.
  rewrite ?node_5086.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2271_nr_5F2300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2271_nr_5F2300 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5088 (s : N.State) (i : N.Inputs) :
  R.v5088 (state s) (inputs i) = Zmod.unsigned (N.v5088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5088 s i)) at 1.
  unfold R.v5088, N.v5088.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5089 (s : N.State) (i : N.Inputs) :
  R.v5089 (state s) (inputs i) = Zmod.unsigned (N.v5089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5089 s i)) at 1.
  unfold R.v5089, N.v5089.
  rewrite ?node_5088.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2272_nr_5F2301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2272_nr_5F2301 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5090 (s : N.State) (i : N.Inputs) :
  R.v5090 (state s) (inputs i) = Zmod.unsigned (N.v5090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5090 s i)) at 1.
  unfold R.v5090, N.v5090.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5091 (s : N.State) (i : N.Inputs) :
  R.v5091 (state s) (inputs i) = Zmod.unsigned (N.v5091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5091 s i)) at 1.
  unfold R.v5091, N.v5091.
  rewrite ?node_5090.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2273_nr_5F2303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2273_nr_5F2303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5092 (s : N.State) (i : N.Inputs) :
  R.v5092 (state s) (inputs i) = Zmod.unsigned (N.v5092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5092 s i)) at 1.
  unfold R.v5092, N.v5092.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5093 (s : N.State) (i : N.Inputs) :
  R.v5093 (state s) (inputs i) = Zmod.unsigned (N.v5093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5093 s i)) at 1.
  unfold R.v5093, N.v5093.
  rewrite ?node_5092.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2274_nr_5F2304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2274_nr_5F2304 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5094 (s : N.State) (i : N.Inputs) :
  R.v5094 (state s) (inputs i) = Zmod.unsigned (N.v5094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5094 s i)) at 1.
  unfold R.v5094, N.v5094.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5095 (s : N.State) (i : N.Inputs) :
  R.v5095 (state s) (inputs i) = Zmod.unsigned (N.v5095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5095 s i)) at 1.
  unfold R.v5095, N.v5095.
  unfold R.v3021, N.v3021.
  rewrite ?node_5094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5096 (s : N.State) (i : N.Inputs) :
  R.v5096 (state s) (inputs i) = Zmod.unsigned (N.v5096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5096 s i)) at 1.
  unfold R.v5096, N.v5096.
  rewrite ?node_5095.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2275_nr_5F2305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2275_nr_5F2305 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5097 (s : N.State) (i : N.Inputs) :
  R.v5097 (state s) (inputs i) = Zmod.unsigned (N.v5097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5097 s i)) at 1.
  unfold R.v5097, N.v5097.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5098 (s : N.State) (i : N.Inputs) :
  R.v5098 (state s) (inputs i) = Zmod.unsigned (N.v5098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5098 s i)) at 1.
  unfold R.v5098, N.v5098.
  rewrite ?node_5097.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2276_nr_5F2306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2276_nr_5F2306 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5099 (s : N.State) (i : N.Inputs) :
  R.v5099 (state s) (inputs i) = Zmod.unsigned (N.v5099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5099 s i)) at 1.
  unfold R.v5099, N.v5099.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5100 (s : N.State) (i : N.Inputs) :
  R.v5100 (state s) (inputs i) = Zmod.unsigned (N.v5100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5100 s i)) at 1.
  unfold R.v5100, N.v5100.
  rewrite ?node_5099.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2277_nr_5F2308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2277_nr_5F2308 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5101 (s : N.State) (i : N.Inputs) :
  R.v5101 (state s) (inputs i) = Zmod.unsigned (N.v5101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5101 s i)) at 1.
  unfold R.v5101, N.v5101.
  rewrite !state_r0_nr.
  rewrite !state_r1_nr_5F1.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r0_nr s)).
  rewrite ?(bits.mod_to_Z (N.r1_nr_5F1 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5102 (s : N.State) (i : N.Inputs) :
  R.v5102 (state s) (inputs i) = Zmod.unsigned (N.v5102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5102 s i)) at 1.
  unfold R.v5102, N.v5102.
  rewrite ?node_5101.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2278_nr_5F2309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2278_nr_5F2309 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5103 (s : N.State) (i : N.Inputs) :
  R.v5103 (state s) (inputs i) = Zmod.unsigned (N.v5103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5103 s i)) at 1.
  unfold R.v5103, N.v5103.
  rewrite !state_r2_nr_5F2.
  rewrite !state_r3_nr_5F3.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2_nr_5F2 s)).
  rewrite ?(bits.mod_to_Z (N.r3_nr_5F3 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5104 (s : N.State) (i : N.Inputs) :
  R.v5104 (state s) (inputs i) = Zmod.unsigned (N.v5104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5104 s i)) at 1.
  unfold R.v5104, N.v5104.
  rewrite !state_r0_nr.
  rewrite !state_r1_nr_5F1.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r0_nr s)).
  rewrite ?(bits.mod_to_Z (N.r1_nr_5F1 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5105 (s : N.State) (i : N.Inputs) :
  R.v5105 (state s) (inputs i) = Zmod.unsigned (N.v5105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5105 s i)) at 1.
  unfold R.v5105, N.v5105.
  rewrite ?node_5103.
  rewrite ?node_5104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5106 (s : N.State) (i : N.Inputs) :
  R.v5106 (state s) (inputs i) = Zmod.unsigned (N.v5106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5106 s i)) at 1.
  unfold R.v5106, N.v5106.
  rewrite ?node_5105.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2279_nr_5F2310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2279_nr_5F2310 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5107 (s : N.State) (i : N.Inputs) :
  R.v5107 (state s) (inputs i) = Zmod.unsigned (N.v5107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5107 s i)) at 1.
  unfold R.v5107, N.v5107.
  rewrite !state_r4_nr_5F4.
  rewrite !state_r5_nr_5F5.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r4_nr_5F4 s)).
  rewrite ?(bits.mod_to_Z (N.r5_nr_5F5 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5108 (s : N.State) (i : N.Inputs) :
  R.v5108 (state s) (inputs i) = Zmod.unsigned (N.v5108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5108 s i)) at 1.
  unfold R.v5108, N.v5108.
  rewrite ?node_5107.
  rewrite !state_r6_nr_5F6.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r6_nr_5F6 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5109 (s : N.State) (i : N.Inputs) :
  R.v5109 (state s) (inputs i) = Zmod.unsigned (N.v5109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5109 s i)) at 1.
  unfold R.v5109, N.v5109.
  rewrite !state_r2_nr_5F2.
  rewrite !state_r3_nr_5F3.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2_nr_5F2 s)).
  rewrite ?(bits.mod_to_Z (N.r3_nr_5F3 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5110 (s : N.State) (i : N.Inputs) :
  R.v5110 (state s) (inputs i) = Zmod.unsigned (N.v5110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5110 s i)) at 1.
  unfold R.v5110, N.v5110.
  rewrite ?node_5108.
  rewrite ?node_5109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5111 (s : N.State) (i : N.Inputs) :
  R.v5111 (state s) (inputs i) = Zmod.unsigned (N.v5111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5111 s i)) at 1.
  unfold R.v5111, N.v5111.
  rewrite ?node_5103.
  rewrite ?node_5104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5112 (s : N.State) (i : N.Inputs) :
  R.v5112 (state s) (inputs i) = Zmod.unsigned (N.v5112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5112 s i)) at 1.
  unfold R.v5112, N.v5112.
  rewrite ?node_5110.
  rewrite ?node_5111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5113 (s : N.State) (i : N.Inputs) :
  R.v5113 (state s) (inputs i) = Zmod.unsigned (N.v5113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5113 s i)) at 1.
  unfold R.v5113, N.v5113.
  rewrite ?node_5112.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2280_nr_5F2311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2280_nr_5F2311 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5114 (s : N.State) (i : N.Inputs) :
  R.v5114 (state s) (inputs i) = Zmod.unsigned (N.v5114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5114 s i)) at 1.
  unfold R.v5114, N.v5114.
  rewrite !state_r7_nr_5F7.
  rewrite !state_r8_nr_5F8.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r7_nr_5F7 s)).
  rewrite ?(bits.mod_to_Z (N.r8_nr_5F8 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5115 (s : N.State) (i : N.Inputs) :
  R.v5115 (state s) (inputs i) = Zmod.unsigned (N.v5115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5115 s i)) at 1.
  unfold R.v5115, N.v5115.
  rewrite ?node_5114.
  rewrite !state_r9_nr_5F9.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r9_nr_5F9 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5116 (s : N.State) (i : N.Inputs) :
  R.v5116 (state s) (inputs i) = Zmod.unsigned (N.v5116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5116 s i)) at 1.
  unfold R.v5116, N.v5116.
  rewrite !state_r4_nr_5F4.
  rewrite !state_r5_nr_5F5.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r4_nr_5F4 s)).
  rewrite ?(bits.mod_to_Z (N.r5_nr_5F5 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5117 (s : N.State) (i : N.Inputs) :
  R.v5117 (state s) (inputs i) = Zmod.unsigned (N.v5117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5117 s i)) at 1.
  unfold R.v5117, N.v5117.
  rewrite ?node_5107.
  rewrite !state_r6_nr_5F6.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r6_nr_5F6 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5118 (s : N.State) (i : N.Inputs) :
  R.v5118 (state s) (inputs i) = Zmod.unsigned (N.v5118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5118 s i)) at 1.
  unfold R.v5118, N.v5118.
  rewrite ?node_5116.
  rewrite ?node_5117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5119 (s : N.State) (i : N.Inputs) :
  R.v5119 (state s) (inputs i) = Zmod.unsigned (N.v5119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5119 s i)) at 1.
  unfold R.v5119, N.v5119.
  rewrite ?node_5115.
  rewrite ?node_5118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5120 (s : N.State) (i : N.Inputs) :
  R.v5120 (state s) (inputs i) = Zmod.unsigned (N.v5120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5120 s i)) at 1.
  unfold R.v5120, N.v5120.
  rewrite ?node_5108.
  rewrite ?node_5109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5121 (s : N.State) (i : N.Inputs) :
  R.v5121 (state s) (inputs i) = Zmod.unsigned (N.v5121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5121 s i)) at 1.
  unfold R.v5121, N.v5121.
  rewrite ?node_5119.
  rewrite ?node_5120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5122 (s : N.State) (i : N.Inputs) :
  R.v5122 (state s) (inputs i) = Zmod.unsigned (N.v5122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5122 s i)) at 1.
  unfold R.v5122, N.v5122.
  rewrite ?node_5110.
  rewrite ?node_5111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5123 (s : N.State) (i : N.Inputs) :
  R.v5123 (state s) (inputs i) = Zmod.unsigned (N.v5123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5123 s i)) at 1.
  unfold R.v5123, N.v5123.
  rewrite ?node_5121.
  rewrite ?node_5122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5124 (s : N.State) (i : N.Inputs) :
  R.v5124 (state s) (inputs i) = Zmod.unsigned (N.v5124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5124 s i)) at 1.
  unfold R.v5124, N.v5124.
  rewrite ?node_5123.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2281_nr_5F2312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2281_nr_5F2312 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5125 (s : N.State) (i : N.Inputs) :
  R.v5125 (state s) (inputs i) = Zmod.unsigned (N.v5125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5125 s i)) at 1.
  unfold R.v5125, N.v5125.
  rewrite !state_r10_nr_5F10.
  rewrite !state_r11_nr_5F11.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r10_nr_5F10 s)).
  rewrite ?(bits.mod_to_Z (N.r11_nr_5F11 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5126 (s : N.State) (i : N.Inputs) :
  R.v5126 (state s) (inputs i) = Zmod.unsigned (N.v5126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5126 s i)) at 1.
  unfold R.v5126, N.v5126.
  rewrite ?node_5125.
  rewrite !state_r12_nr_5F12.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r12_nr_5F12 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5127 (s : N.State) (i : N.Inputs) :
  R.v5127 (state s) (inputs i) = Zmod.unsigned (N.v5127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5127 s i)) at 1.
  unfold R.v5127, N.v5127.
  rewrite ?node_5126.
  rewrite !state_r13_nr_5F13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r13_nr_5F13 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5128 (s : N.State) (i : N.Inputs) :
  R.v5128 (state s) (inputs i) = Zmod.unsigned (N.v5128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5128 s i)) at 1.
  unfold R.v5128, N.v5128.
  rewrite !state_r7_nr_5F7.
  rewrite !state_r8_nr_5F8.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r7_nr_5F7 s)).
  rewrite ?(bits.mod_to_Z (N.r8_nr_5F8 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5129 (s : N.State) (i : N.Inputs) :
  R.v5129 (state s) (inputs i) = Zmod.unsigned (N.v5129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5129 s i)) at 1.
  unfold R.v5129, N.v5129.
  rewrite ?node_5114.
  rewrite !state_r9_nr_5F9.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r9_nr_5F9 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5130 (s : N.State) (i : N.Inputs) :
  R.v5130 (state s) (inputs i) = Zmod.unsigned (N.v5130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5130 s i)) at 1.
  unfold R.v5130, N.v5130.
  rewrite ?node_5128.
  rewrite ?node_5129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5131 (s : N.State) (i : N.Inputs) :
  R.v5131 (state s) (inputs i) = Zmod.unsigned (N.v5131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5131 s i)) at 1.
  unfold R.v5131, N.v5131.
  rewrite ?node_5127.
  rewrite ?node_5130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5132 (s : N.State) (i : N.Inputs) :
  R.v5132 (state s) (inputs i) = Zmod.unsigned (N.v5132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5132 s i)) at 1.
  unfold R.v5132, N.v5132.
  rewrite ?node_5115.
  rewrite ?node_5118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5133 (s : N.State) (i : N.Inputs) :
  R.v5133 (state s) (inputs i) = Zmod.unsigned (N.v5133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5133 s i)) at 1.
  unfold R.v5133, N.v5133.
  rewrite ?node_5131.
  rewrite ?node_5132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5134 (s : N.State) (i : N.Inputs) :
  R.v5134 (state s) (inputs i) = Zmod.unsigned (N.v5134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5134 s i)) at 1.
  unfold R.v5134, N.v5134.
  rewrite ?node_5119.
  rewrite ?node_5120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5135 (s : N.State) (i : N.Inputs) :
  R.v5135 (state s) (inputs i) = Zmod.unsigned (N.v5135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5135 s i)) at 1.
  unfold R.v5135, N.v5135.
  rewrite ?node_5133.
  rewrite ?node_5134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5136 (s : N.State) (i : N.Inputs) :
  R.v5136 (state s) (inputs i) = Zmod.unsigned (N.v5136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5136 s i)) at 1.
  unfold R.v5136, N.v5136.
  rewrite ?node_5121.
  rewrite ?node_5122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5137 (s : N.State) (i : N.Inputs) :
  R.v5137 (state s) (inputs i) = Zmod.unsigned (N.v5137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5137 s i)) at 1.
  unfold R.v5137, N.v5137.
  rewrite ?node_5135.
  rewrite ?node_5136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5138 (s : N.State) (i : N.Inputs) :
  R.v5138 (state s) (inputs i) = Zmod.unsigned (N.v5138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5138 s i)) at 1.
  unfold R.v5138, N.v5138.
  rewrite ?node_5137.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2282_nr_5F2313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2282_nr_5F2313 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5139 (s : N.State) (i : N.Inputs) :
  R.v5139 (state s) (inputs i) = Zmod.unsigned (N.v5139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5139 s i)) at 1.
  unfold R.v5139, N.v5139.
  rewrite !state_r14_nr_5F14.
  rewrite !state_r15_nr_5F15.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r14_nr_5F14 s)).
  rewrite ?(bits.mod_to_Z (N.r15_nr_5F15 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5140 (s : N.State) (i : N.Inputs) :
  R.v5140 (state s) (inputs i) = Zmod.unsigned (N.v5140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5140 s i)) at 1.
  unfold R.v5140, N.v5140.
  rewrite ?node_5139.
  rewrite !state_r16_nr_5F16.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r16_nr_5F16 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5141 (s : N.State) (i : N.Inputs) :
  R.v5141 (state s) (inputs i) = Zmod.unsigned (N.v5141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5141 s i)) at 1.
  unfold R.v5141, N.v5141.
  rewrite ?node_5140.
  rewrite !state_r17_nr_5F17.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r17_nr_5F17 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5142 (s : N.State) (i : N.Inputs) :
  R.v5142 (state s) (inputs i) = Zmod.unsigned (N.v5142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5142 s i)) at 1.
  unfold R.v5142, N.v5142.
  rewrite !state_r10_nr_5F10.
  rewrite !state_r11_nr_5F11.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r10_nr_5F10 s)).
  rewrite ?(bits.mod_to_Z (N.r11_nr_5F11 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5143 (s : N.State) (i : N.Inputs) :
  R.v5143 (state s) (inputs i) = Zmod.unsigned (N.v5143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5143 s i)) at 1.
  unfold R.v5143, N.v5143.
  rewrite ?node_5125.
  rewrite !state_r12_nr_5F12.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r12_nr_5F12 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5144 (s : N.State) (i : N.Inputs) :
  R.v5144 (state s) (inputs i) = Zmod.unsigned (N.v5144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5144 s i)) at 1.
  unfold R.v5144, N.v5144.
  rewrite ?node_5142.
  rewrite ?node_5143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5145 (s : N.State) (i : N.Inputs) :
  R.v5145 (state s) (inputs i) = Zmod.unsigned (N.v5145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5145 s i)) at 1.
  unfold R.v5145, N.v5145.
  rewrite ?node_5141.
  rewrite ?node_5144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5146 (s : N.State) (i : N.Inputs) :
  R.v5146 (state s) (inputs i) = Zmod.unsigned (N.v5146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5146 s i)) at 1.
  unfold R.v5146, N.v5146.
  rewrite ?node_5126.
  rewrite !state_r13_nr_5F13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r13_nr_5F13 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5147 (s : N.State) (i : N.Inputs) :
  R.v5147 (state s) (inputs i) = Zmod.unsigned (N.v5147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5147 s i)) at 1.
  unfold R.v5147, N.v5147.
  rewrite ?node_5145.
  rewrite ?node_5146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5148 (s : N.State) (i : N.Inputs) :
  R.v5148 (state s) (inputs i) = Zmod.unsigned (N.v5148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5148 s i)) at 1.
  unfold R.v5148, N.v5148.
  rewrite ?node_5127.
  rewrite ?node_5130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5149 (s : N.State) (i : N.Inputs) :
  R.v5149 (state s) (inputs i) = Zmod.unsigned (N.v5149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5149 s i)) at 1.
  unfold R.v5149, N.v5149.
  rewrite ?node_5147.
  rewrite ?node_5148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5150 (s : N.State) (i : N.Inputs) :
  R.v5150 (state s) (inputs i) = Zmod.unsigned (N.v5150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5150 s i)) at 1.
  unfold R.v5150, N.v5150.
  rewrite ?node_5131.
  rewrite ?node_5132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5151 (s : N.State) (i : N.Inputs) :
  R.v5151 (state s) (inputs i) = Zmod.unsigned (N.v5151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5151 s i)) at 1.
  unfold R.v5151, N.v5151.
  rewrite ?node_5149.
  rewrite ?node_5150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5152 (s : N.State) (i : N.Inputs) :
  R.v5152 (state s) (inputs i) = Zmod.unsigned (N.v5152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5152 s i)) at 1.
  unfold R.v5152, N.v5152.
  rewrite ?node_5133.
  rewrite ?node_5134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5153 (s : N.State) (i : N.Inputs) :
  R.v5153 (state s) (inputs i) = Zmod.unsigned (N.v5153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5153 s i)) at 1.
  unfold R.v5153, N.v5153.
  rewrite ?node_5151.
  rewrite ?node_5152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5154 (s : N.State) (i : N.Inputs) :
  R.v5154 (state s) (inputs i) = Zmod.unsigned (N.v5154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5154 s i)) at 1.
  unfold R.v5154, N.v5154.
  rewrite ?node_5153.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2283_nr_5F2314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2283_nr_5F2314 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5155 (s : N.State) (i : N.Inputs) :
  R.v5155 (state s) (inputs i) = Zmod.unsigned (N.v5155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5155 s i)) at 1.
  unfold R.v5155, N.v5155.
  rewrite ?node_5135.
  rewrite ?node_5136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5156 (s : N.State) (i : N.Inputs) :
  R.v5156 (state s) (inputs i) = Zmod.unsigned (N.v5156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5156 s i)) at 1.
  unfold R.v5156, N.v5156.
  rewrite ?node_5155.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2284_nr_5F2315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2284_nr_5F2315 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5157 (s : N.State) (i : N.Inputs) :
  R.v5157 (state s) (inputs i) = Zmod.unsigned (N.v5157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5157 s i)) at 1.
  unfold R.v5157, N.v5157.
  rewrite !state_r18_nr_5F18.
  rewrite !state_r19_nr_5F19.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r18_nr_5F18 s)).
  rewrite ?(bits.mod_to_Z (N.r19_nr_5F19 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5158 (s : N.State) (i : N.Inputs) :
  R.v5158 (state s) (inputs i) = Zmod.unsigned (N.v5158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5158 s i)) at 1.
  unfold R.v5158, N.v5158.
  rewrite ?node_5157.
  rewrite !state_r20_nr_5F20.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r20_nr_5F20 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5159 (s : N.State) (i : N.Inputs) :
  R.v5159 (state s) (inputs i) = Zmod.unsigned (N.v5159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5159 s i)) at 1.
  unfold R.v5159, N.v5159.
  rewrite ?node_5158.
  rewrite !state_r21_nr_5F21.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r21_nr_5F21 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5160 (s : N.State) (i : N.Inputs) :
  R.v5160 (state s) (inputs i) = Zmod.unsigned (N.v5160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5160 s i)) at 1.
  unfold R.v5160, N.v5160.
  rewrite !state_r14_nr_5F14.
  rewrite !state_r15_nr_5F15.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r14_nr_5F14 s)).
  rewrite ?(bits.mod_to_Z (N.r15_nr_5F15 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5161 (s : N.State) (i : N.Inputs) :
  R.v5161 (state s) (inputs i) = Zmod.unsigned (N.v5161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5161 s i)) at 1.
  unfold R.v5161, N.v5161.
  rewrite ?node_5139.
  rewrite !state_r16_nr_5F16.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r16_nr_5F16 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5162 (s : N.State) (i : N.Inputs) :
  R.v5162 (state s) (inputs i) = Zmod.unsigned (N.v5162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5162 s i)) at 1.
  unfold R.v5162, N.v5162.
  rewrite ?node_5160.
  rewrite ?node_5161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5163 (s : N.State) (i : N.Inputs) :
  R.v5163 (state s) (inputs i) = Zmod.unsigned (N.v5163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5163 s i)) at 1.
  unfold R.v5163, N.v5163.
  rewrite ?node_5159.
  rewrite ?node_5162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5164 (s : N.State) (i : N.Inputs) :
  R.v5164 (state s) (inputs i) = Zmod.unsigned (N.v5164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5164 s i)) at 1.
  unfold R.v5164, N.v5164.
  rewrite ?node_5163.
  rewrite !state_r22_nr_5F22.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r22_nr_5F22 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5165 (s : N.State) (i : N.Inputs) :
  R.v5165 (state s) (inputs i) = Zmod.unsigned (N.v5165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5165 s i)) at 1.
  unfold R.v5165, N.v5165.
  rewrite ?node_5140.
  rewrite !state_r17_nr_5F17.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r17_nr_5F17 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5166 (s : N.State) (i : N.Inputs) :
  R.v5166 (state s) (inputs i) = Zmod.unsigned (N.v5166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5166 s i)) at 1.
  unfold R.v5166, N.v5166.
  rewrite ?node_5141.
  rewrite ?node_5144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5167 (s : N.State) (i : N.Inputs) :
  R.v5167 (state s) (inputs i) = Zmod.unsigned (N.v5167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5167 s i)) at 1.
  unfold R.v5167, N.v5167.
  rewrite ?node_5165.
  rewrite ?node_5166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5168 (s : N.State) (i : N.Inputs) :
  R.v5168 (state s) (inputs i) = Zmod.unsigned (N.v5168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5168 s i)) at 1.
  unfold R.v5168, N.v5168.
  rewrite ?node_5164.
  rewrite ?node_5167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5169 (s : N.State) (i : N.Inputs) :
  R.v5169 (state s) (inputs i) = Zmod.unsigned (N.v5169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5169 s i)) at 1.
  unfold R.v5169, N.v5169.
  rewrite ?node_5145.
  rewrite ?node_5146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5170 (s : N.State) (i : N.Inputs) :
  R.v5170 (state s) (inputs i) = Zmod.unsigned (N.v5170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5170 s i)) at 1.
  unfold R.v5170, N.v5170.
  rewrite ?node_5168.
  rewrite ?node_5169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5171 (s : N.State) (i : N.Inputs) :
  R.v5171 (state s) (inputs i) = Zmod.unsigned (N.v5171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5171 s i)) at 1.
  unfold R.v5171, N.v5171.
  rewrite ?node_5147.
  rewrite ?node_5148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5172 (s : N.State) (i : N.Inputs) :
  R.v5172 (state s) (inputs i) = Zmod.unsigned (N.v5172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5172 s i)) at 1.
  unfold R.v5172, N.v5172.
  rewrite ?node_5170.
  rewrite ?node_5171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5173 (s : N.State) (i : N.Inputs) :
  R.v5173 (state s) (inputs i) = Zmod.unsigned (N.v5173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5173 s i)) at 1.
  unfold R.v5173, N.v5173.
  rewrite ?node_5149.
  rewrite ?node_5150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5174 (s : N.State) (i : N.Inputs) :
  R.v5174 (state s) (inputs i) = Zmod.unsigned (N.v5174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5174 s i)) at 1.
  unfold R.v5174, N.v5174.
  rewrite ?node_5172.
  rewrite ?node_5173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5175 (s : N.State) (i : N.Inputs) :
  R.v5175 (state s) (inputs i) = Zmod.unsigned (N.v5175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5175 s i)) at 1.
  unfold R.v5175, N.v5175.
  rewrite ?node_5174.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2285_nr_5F2316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2285_nr_5F2316 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5176 (s : N.State) (i : N.Inputs) :
  R.v5176 (state s) (inputs i) = Zmod.unsigned (N.v5176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5176 s i)) at 1.
  unfold R.v5176, N.v5176.
  rewrite ?node_5151.
  rewrite ?node_5152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5177 (s : N.State) (i : N.Inputs) :
  R.v5177 (state s) (inputs i) = Zmod.unsigned (N.v5177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5177 s i)) at 1.
  unfold R.v5177, N.v5177.
  rewrite ?node_5176.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2286_nr_5F2317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2286_nr_5F2317 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5178 (s : N.State) (i : N.Inputs) :
  R.v5178 (state s) (inputs i) = Zmod.unsigned (N.v5178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5178 s i)) at 1.
  unfold R.v5178, N.v5178.
  rewrite !state_r23_nr_5F23.
  rewrite !state_r24_nr_5F24.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r23_nr_5F23 s)).
  rewrite ?(bits.mod_to_Z (N.r24_nr_5F24 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5179 (s : N.State) (i : N.Inputs) :
  R.v5179 (state s) (inputs i) = Zmod.unsigned (N.v5179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5179 s i)) at 1.
  unfold R.v5179, N.v5179.
  rewrite ?node_5178.
  rewrite !state_r25_nr_5F25.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r25_nr_5F25 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5180 (s : N.State) (i : N.Inputs) :
  R.v5180 (state s) (inputs i) = Zmod.unsigned (N.v5180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5180 s i)) at 1.
  unfold R.v5180, N.v5180.
  rewrite ?node_5179.
  rewrite !state_r26_nr_5F26.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r26_nr_5F26 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5181 (s : N.State) (i : N.Inputs) :
  R.v5181 (state s) (inputs i) = Zmod.unsigned (N.v5181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5181 s i)) at 1.
  unfold R.v5181, N.v5181.
  rewrite !state_r18_nr_5F18.
  rewrite !state_r19_nr_5F19.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r18_nr_5F18 s)).
  rewrite ?(bits.mod_to_Z (N.r19_nr_5F19 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5182 (s : N.State) (i : N.Inputs) :
  R.v5182 (state s) (inputs i) = Zmod.unsigned (N.v5182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5182 s i)) at 1.
  unfold R.v5182, N.v5182.
  rewrite ?node_5157.
  rewrite !state_r20_nr_5F20.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r20_nr_5F20 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5183 (s : N.State) (i : N.Inputs) :
  R.v5183 (state s) (inputs i) = Zmod.unsigned (N.v5183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5183 s i)) at 1.
  unfold R.v5183, N.v5183.
  rewrite ?node_5181.
  rewrite ?node_5182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5184 (s : N.State) (i : N.Inputs) :
  R.v5184 (state s) (inputs i) = Zmod.unsigned (N.v5184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5184 s i)) at 1.
  unfold R.v5184, N.v5184.
  rewrite ?node_5180.
  rewrite ?node_5183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5185 (s : N.State) (i : N.Inputs) :
  R.v5185 (state s) (inputs i) = Zmod.unsigned (N.v5185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5185 s i)) at 1.
  unfold R.v5185, N.v5185.
  rewrite ?node_5184.
  rewrite !state_r27_nr_5F27.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r27_nr_5F27 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5186 (s : N.State) (i : N.Inputs) :
  R.v5186 (state s) (inputs i) = Zmod.unsigned (N.v5186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5186 s i)) at 1.
  unfold R.v5186, N.v5186.
  rewrite ?node_5158.
  rewrite !state_r21_nr_5F21.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r21_nr_5F21 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5187 (s : N.State) (i : N.Inputs) :
  R.v5187 (state s) (inputs i) = Zmod.unsigned (N.v5187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5187 s i)) at 1.
  unfold R.v5187, N.v5187.
  rewrite ?node_5159.
  rewrite ?node_5162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5188 (s : N.State) (i : N.Inputs) :
  R.v5188 (state s) (inputs i) = Zmod.unsigned (N.v5188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5188 s i)) at 1.
  unfold R.v5188, N.v5188.
  rewrite ?node_5186.
  rewrite ?node_5187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5189 (s : N.State) (i : N.Inputs) :
  R.v5189 (state s) (inputs i) = Zmod.unsigned (N.v5189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5189 s i)) at 1.
  unfold R.v5189, N.v5189.
  rewrite ?node_5185.
  rewrite ?node_5188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5190 (s : N.State) (i : N.Inputs) :
  R.v5190 (state s) (inputs i) = Zmod.unsigned (N.v5190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5190 s i)) at 1.
  unfold R.v5190, N.v5190.
  rewrite ?node_5163.
  rewrite !state_r22_nr_5F22.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r22_nr_5F22 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5191 (s : N.State) (i : N.Inputs) :
  R.v5191 (state s) (inputs i) = Zmod.unsigned (N.v5191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5191 s i)) at 1.
  unfold R.v5191, N.v5191.
  rewrite ?node_5164.
  rewrite ?node_5167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5192 (s : N.State) (i : N.Inputs) :
  R.v5192 (state s) (inputs i) = Zmod.unsigned (N.v5192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5192 s i)) at 1.
  unfold R.v5192, N.v5192.
  rewrite ?node_5190.
  rewrite ?node_5191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5193 (s : N.State) (i : N.Inputs) :
  R.v5193 (state s) (inputs i) = Zmod.unsigned (N.v5193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5193 s i)) at 1.
  unfold R.v5193, N.v5193.
  rewrite ?node_5189.
  rewrite ?node_5192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5194 (s : N.State) (i : N.Inputs) :
  R.v5194 (state s) (inputs i) = Zmod.unsigned (N.v5194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5194 s i)) at 1.
  unfold R.v5194, N.v5194.
  rewrite ?node_5168.
  rewrite ?node_5169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5195 (s : N.State) (i : N.Inputs) :
  R.v5195 (state s) (inputs i) = Zmod.unsigned (N.v5195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5195 s i)) at 1.
  unfold R.v5195, N.v5195.
  rewrite ?node_5193.
  rewrite ?node_5194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5196 (s : N.State) (i : N.Inputs) :
  R.v5196 (state s) (inputs i) = Zmod.unsigned (N.v5196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5196 s i)) at 1.
  unfold R.v5196, N.v5196.
  rewrite ?node_5170.
  rewrite ?node_5171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5197 (s : N.State) (i : N.Inputs) :
  R.v5197 (state s) (inputs i) = Zmod.unsigned (N.v5197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5197 s i)) at 1.
  unfold R.v5197, N.v5197.
  rewrite ?node_5195.
  rewrite ?node_5196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5198 (s : N.State) (i : N.Inputs) :
  R.v5198 (state s) (inputs i) = Zmod.unsigned (N.v5198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5198 s i)) at 1.
  unfold R.v5198, N.v5198.
  rewrite ?node_5197.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2287_nr_5F2318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2287_nr_5F2318 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5199 (s : N.State) (i : N.Inputs) :
  R.v5199 (state s) (inputs i) = Zmod.unsigned (N.v5199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5199 s i)) at 1.
  unfold R.v5199, N.v5199.
  rewrite ?node_5172.
  rewrite ?node_5173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5200 (s : N.State) (i : N.Inputs) :
  R.v5200 (state s) (inputs i) = Zmod.unsigned (N.v5200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5200 s i)) at 1.
  unfold R.v5200, N.v5200.
  rewrite ?node_5199.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2288_nr_5F2319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2288_nr_5F2319 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5201 (s : N.State) (i : N.Inputs) :
  R.v5201 (state s) (inputs i) = Zmod.unsigned (N.v5201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5201 s i)) at 1.
  unfold R.v5201, N.v5201.
  rewrite !state_r28_nr_5F28.
  rewrite !state_r29_nr_5F29.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r28_nr_5F28 s)).
  rewrite ?(bits.mod_to_Z (N.r29_nr_5F29 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5202 (s : N.State) (i : N.Inputs) :
  R.v5202 (state s) (inputs i) = Zmod.unsigned (N.v5202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5202 s i)) at 1.
  unfold R.v5202, N.v5202.
  rewrite ?node_5201.
  rewrite !state_r30_nr_5F30.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r30_nr_5F30 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5203 (s : N.State) (i : N.Inputs) :
  R.v5203 (state s) (inputs i) = Zmod.unsigned (N.v5203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5203 s i)) at 1.
  unfold R.v5203, N.v5203.
  rewrite ?node_5202.
  rewrite !state_r31_nr_5F31.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r31_nr_5F31 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5204 (s : N.State) (i : N.Inputs) :
  R.v5204 (state s) (inputs i) = Zmod.unsigned (N.v5204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5204 s i)) at 1.
  unfold R.v5204, N.v5204.
  rewrite !state_r23_nr_5F23.
  rewrite !state_r24_nr_5F24.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r23_nr_5F23 s)).
  rewrite ?(bits.mod_to_Z (N.r24_nr_5F24 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5205 (s : N.State) (i : N.Inputs) :
  R.v5205 (state s) (inputs i) = Zmod.unsigned (N.v5205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5205 s i)) at 1.
  unfold R.v5205, N.v5205.
  rewrite ?node_5178.
  rewrite !state_r25_nr_5F25.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r25_nr_5F25 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5206 (s : N.State) (i : N.Inputs) :
  R.v5206 (state s) (inputs i) = Zmod.unsigned (N.v5206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5206 s i)) at 1.
  unfold R.v5206, N.v5206.
  rewrite ?node_5204.
  rewrite ?node_5205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5207 (s : N.State) (i : N.Inputs) :
  R.v5207 (state s) (inputs i) = Zmod.unsigned (N.v5207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5207 s i)) at 1.
  unfold R.v5207, N.v5207.
  rewrite ?node_5203.
  rewrite ?node_5206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5208 (s : N.State) (i : N.Inputs) :
  R.v5208 (state s) (inputs i) = Zmod.unsigned (N.v5208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5208 s i)) at 1.
  unfold R.v5208, N.v5208.
  rewrite !state_r32_nr_5F32.
  rewrite !state_r33_nr_5F33.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r32_nr_5F32 s)).
  rewrite ?(bits.mod_to_Z (N.r33_nr_5F33 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5209 (s : N.State) (i : N.Inputs) :
  R.v5209 (state s) (inputs i) = Zmod.unsigned (N.v5209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5209 s i)) at 1.
  unfold R.v5209, N.v5209.
  rewrite ?node_5207.
  rewrite ?node_5208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5210 (s : N.State) (i : N.Inputs) :
  R.v5210 (state s) (inputs i) = Zmod.unsigned (N.v5210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5210 s i)) at 1.
  unfold R.v5210, N.v5210.
  rewrite ?node_5179.
  rewrite !state_r26_nr_5F26.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r26_nr_5F26 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5211 (s : N.State) (i : N.Inputs) :
  R.v5211 (state s) (inputs i) = Zmod.unsigned (N.v5211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5211 s i)) at 1.
  unfold R.v5211, N.v5211.
  rewrite ?node_5180.
  rewrite ?node_5183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5212 (s : N.State) (i : N.Inputs) :
  R.v5212 (state s) (inputs i) = Zmod.unsigned (N.v5212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5212 s i)) at 1.
  unfold R.v5212, N.v5212.
  rewrite ?node_5210.
  rewrite ?node_5211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5213 (s : N.State) (i : N.Inputs) :
  R.v5213 (state s) (inputs i) = Zmod.unsigned (N.v5213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5213 s i)) at 1.
  unfold R.v5213, N.v5213.
  rewrite ?node_5209.
  rewrite ?node_5212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5214 (s : N.State) (i : N.Inputs) :
  R.v5214 (state s) (inputs i) = Zmod.unsigned (N.v5214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5214 s i)) at 1.
  unfold R.v5214, N.v5214.
  rewrite ?node_5184.
  rewrite !state_r27_nr_5F27.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r27_nr_5F27 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5215 (s : N.State) (i : N.Inputs) :
  R.v5215 (state s) (inputs i) = Zmod.unsigned (N.v5215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5215 s i)) at 1.
  unfold R.v5215, N.v5215.
  rewrite ?node_5185.
  rewrite ?node_5188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5216 (s : N.State) (i : N.Inputs) :
  R.v5216 (state s) (inputs i) = Zmod.unsigned (N.v5216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5216 s i)) at 1.
  unfold R.v5216, N.v5216.
  rewrite ?node_5214.
  rewrite ?node_5215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5217 (s : N.State) (i : N.Inputs) :
  R.v5217 (state s) (inputs i) = Zmod.unsigned (N.v5217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5217 s i)) at 1.
  unfold R.v5217, N.v5217.
  rewrite ?node_5213.
  rewrite ?node_5216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5218 (s : N.State) (i : N.Inputs) :
  R.v5218 (state s) (inputs i) = Zmod.unsigned (N.v5218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5218 s i)) at 1.
  unfold R.v5218, N.v5218.
  rewrite ?node_5189.
  rewrite ?node_5192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5219 (s : N.State) (i : N.Inputs) :
  R.v5219 (state s) (inputs i) = Zmod.unsigned (N.v5219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5219 s i)) at 1.
  unfold R.v5219, N.v5219.
  rewrite ?node_5217.
  rewrite ?node_5218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5220 (s : N.State) (i : N.Inputs) :
  R.v5220 (state s) (inputs i) = Zmod.unsigned (N.v5220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5220 s i)) at 1.
  unfold R.v5220, N.v5220.
  rewrite ?node_5193.
  rewrite ?node_5194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5221 (s : N.State) (i : N.Inputs) :
  R.v5221 (state s) (inputs i) = Zmod.unsigned (N.v5221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5221 s i)) at 1.
  unfold R.v5221, N.v5221.
  rewrite ?node_5219.
  rewrite ?node_5220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5222 (s : N.State) (i : N.Inputs) :
  R.v5222 (state s) (inputs i) = Zmod.unsigned (N.v5222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5222 s i)) at 1.
  unfold R.v5222, N.v5222.
  rewrite ?node_5221.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2289_nr_5F2320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2289_nr_5F2320 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5223 (s : N.State) (i : N.Inputs) :
  R.v5223 (state s) (inputs i) = Zmod.unsigned (N.v5223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5223 s i)) at 1.
  unfold R.v5223, N.v5223.
  rewrite ?node_5195.
  rewrite ?node_5196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5224 (s : N.State) (i : N.Inputs) :
  R.v5224 (state s) (inputs i) = Zmod.unsigned (N.v5224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5224 s i)) at 1.
  unfold R.v5224, N.v5224.
  rewrite ?node_5223.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2290_nr_5F2321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2290_nr_5F2321 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5225 (s : N.State) (i : N.Inputs) :
  R.v5225 (state s) (inputs i) = Zmod.unsigned (N.v5225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5225 s i)) at 1.
  unfold R.v5225, N.v5225.
  rewrite !state_r34_nr_5F34.
  rewrite !state_r35_nr_5F35.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r34_nr_5F34 s)).
  rewrite ?(bits.mod_to_Z (N.r35_nr_5F35 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5226 (s : N.State) (i : N.Inputs) :
  R.v5226 (state s) (inputs i) = Zmod.unsigned (N.v5226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5226 s i)) at 1.
  unfold R.v5226, N.v5226.
  rewrite ?node_5225.
  rewrite !state_r36_nr_5F36.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r36_nr_5F36 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5227 (s : N.State) (i : N.Inputs) :
  R.v5227 (state s) (inputs i) = Zmod.unsigned (N.v5227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5227 s i)) at 1.
  unfold R.v5227, N.v5227.
  rewrite ?node_5226.
  rewrite !state_r37_nr_5F37.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r37_nr_5F37 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5228 (s : N.State) (i : N.Inputs) :
  R.v5228 (state s) (inputs i) = Zmod.unsigned (N.v5228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5228 s i)) at 1.
  unfold R.v5228, N.v5228.
  rewrite !state_r28_nr_5F28.
  rewrite !state_r29_nr_5F29.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r28_nr_5F28 s)).
  rewrite ?(bits.mod_to_Z (N.r29_nr_5F29 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5229 (s : N.State) (i : N.Inputs) :
  R.v5229 (state s) (inputs i) = Zmod.unsigned (N.v5229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5229 s i)) at 1.
  unfold R.v5229, N.v5229.
  rewrite ?node_5201.
  rewrite !state_r30_nr_5F30.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r30_nr_5F30 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5230 (s : N.State) (i : N.Inputs) :
  R.v5230 (state s) (inputs i) = Zmod.unsigned (N.v5230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5230 s i)) at 1.
  unfold R.v5230, N.v5230.
  rewrite ?node_5228.
  rewrite ?node_5229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5231 (s : N.State) (i : N.Inputs) :
  R.v5231 (state s) (inputs i) = Zmod.unsigned (N.v5231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5231 s i)) at 1.
  unfold R.v5231, N.v5231.
  rewrite ?node_5227.
  rewrite ?node_5230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5232 (s : N.State) (i : N.Inputs) :
  R.v5232 (state s) (inputs i) = Zmod.unsigned (N.v5232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5232 s i)) at 1.
  unfold R.v5232, N.v5232.
  rewrite !state_r38_nr_5F38.
  rewrite !state_r39_nr_5F39.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r38_nr_5F38 s)).
  rewrite ?(bits.mod_to_Z (N.r39_nr_5F39 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5233 (s : N.State) (i : N.Inputs) :
  R.v5233 (state s) (inputs i) = Zmod.unsigned (N.v5233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5233 s i)) at 1.
  unfold R.v5233, N.v5233.
  rewrite ?node_5231.
  rewrite ?node_5232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5234 (s : N.State) (i : N.Inputs) :
  R.v5234 (state s) (inputs i) = Zmod.unsigned (N.v5234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5234 s i)) at 1.
  unfold R.v5234, N.v5234.
  rewrite ?node_5202.
  rewrite !state_r31_nr_5F31.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r31_nr_5F31 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5235 (s : N.State) (i : N.Inputs) :
  R.v5235 (state s) (inputs i) = Zmod.unsigned (N.v5235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5235 s i)) at 1.
  unfold R.v5235, N.v5235.
  rewrite ?node_5203.
  rewrite ?node_5206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5236 (s : N.State) (i : N.Inputs) :
  R.v5236 (state s) (inputs i) = Zmod.unsigned (N.v5236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5236 s i)) at 1.
  unfold R.v5236, N.v5236.
  rewrite ?node_5234.
  rewrite ?node_5235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5237 (s : N.State) (i : N.Inputs) :
  R.v5237 (state s) (inputs i) = Zmod.unsigned (N.v5237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5237 s i)) at 1.
  unfold R.v5237, N.v5237.
  rewrite ?node_5233.
  rewrite ?node_5236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5238 (s : N.State) (i : N.Inputs) :
  R.v5238 (state s) (inputs i) = Zmod.unsigned (N.v5238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5238 s i)) at 1.
  unfold R.v5238, N.v5238.
  rewrite !state_r32_nr_5F32.
  rewrite !state_r33_nr_5F33.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r32_nr_5F32 s)).
  rewrite ?(bits.mod_to_Z (N.r33_nr_5F33 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5239 (s : N.State) (i : N.Inputs) :
  R.v5239 (state s) (inputs i) = Zmod.unsigned (N.v5239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5239 s i)) at 1.
  unfold R.v5239, N.v5239.
  rewrite ?node_5237.
  rewrite ?node_5238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5240 (s : N.State) (i : N.Inputs) :
  R.v5240 (state s) (inputs i) = Zmod.unsigned (N.v5240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5240 s i)) at 1.
  unfold R.v5240, N.v5240.
  rewrite ?node_5207.
  rewrite ?node_5208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5241 (s : N.State) (i : N.Inputs) :
  R.v5241 (state s) (inputs i) = Zmod.unsigned (N.v5241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5241 s i)) at 1.
  unfold R.v5241, N.v5241.
  rewrite ?node_5209.
  rewrite ?node_5212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5242 (s : N.State) (i : N.Inputs) :
  R.v5242 (state s) (inputs i) = Zmod.unsigned (N.v5242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5242 s i)) at 1.
  unfold R.v5242, N.v5242.
  rewrite ?node_5240.
  rewrite ?node_5241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5243 (s : N.State) (i : N.Inputs) :
  R.v5243 (state s) (inputs i) = Zmod.unsigned (N.v5243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5243 s i)) at 1.
  unfold R.v5243, N.v5243.
  rewrite ?node_5239.
  rewrite ?node_5242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5244 (s : N.State) (i : N.Inputs) :
  R.v5244 (state s) (inputs i) = Zmod.unsigned (N.v5244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5244 s i)) at 1.
  unfold R.v5244, N.v5244.
  rewrite ?node_5213.
  rewrite ?node_5216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5245 (s : N.State) (i : N.Inputs) :
  R.v5245 (state s) (inputs i) = Zmod.unsigned (N.v5245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5245 s i)) at 1.
  unfold R.v5245, N.v5245.
  rewrite ?node_5243.
  rewrite ?node_5244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5246 (s : N.State) (i : N.Inputs) :
  R.v5246 (state s) (inputs i) = Zmod.unsigned (N.v5246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5246 s i)) at 1.
  unfold R.v5246, N.v5246.
  rewrite ?node_5217.
  rewrite ?node_5218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5247 (s : N.State) (i : N.Inputs) :
  R.v5247 (state s) (inputs i) = Zmod.unsigned (N.v5247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5247 s i)) at 1.
  unfold R.v5247, N.v5247.
  rewrite ?node_5245.
  rewrite ?node_5246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5248 (s : N.State) (i : N.Inputs) :
  R.v5248 (state s) (inputs i) = Zmod.unsigned (N.v5248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5248 s i)) at 1.
  unfold R.v5248, N.v5248.
  rewrite ?node_5247.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2291_nr_5F2322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2291_nr_5F2322 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5249 (s : N.State) (i : N.Inputs) :
  R.v5249 (state s) (inputs i) = Zmod.unsigned (N.v5249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5249 s i)) at 1.
  unfold R.v5249, N.v5249.
  rewrite ?node_5219.
  rewrite ?node_5220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5250 (s : N.State) (i : N.Inputs) :
  R.v5250 (state s) (inputs i) = Zmod.unsigned (N.v5250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5250 s i)) at 1.
  unfold R.v5250, N.v5250.
  rewrite ?node_5249.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2292_nr_5F2323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2292_nr_5F2323 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5251 (s : N.State) (i : N.Inputs) :
  R.v5251 (state s) (inputs i) = Zmod.unsigned (N.v5251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5251 s i)) at 1.
  unfold R.v5251, N.v5251.
  rewrite !state_r40_nr_5F40.
  rewrite !state_r41_nr_5F41.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r40_nr_5F40 s)).
  rewrite ?(bits.mod_to_Z (N.r41_nr_5F41 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5252 (s : N.State) (i : N.Inputs) :
  R.v5252 (state s) (inputs i) = Zmod.unsigned (N.v5252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5252 s i)) at 1.
  unfold R.v5252, N.v5252.
  rewrite ?node_5251.
  rewrite !state_r42_nr_5F42.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r42_nr_5F42 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5253 (s : N.State) (i : N.Inputs) :
  R.v5253 (state s) (inputs i) = Zmod.unsigned (N.v5253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5253 s i)) at 1.
  unfold R.v5253, N.v5253.
  rewrite ?node_5252.
  rewrite !state_r43_nr_5F43.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r43_nr_5F43 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5254 (s : N.State) (i : N.Inputs) :
  R.v5254 (state s) (inputs i) = Zmod.unsigned (N.v5254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5254 s i)) at 1.
  unfold R.v5254, N.v5254.
  rewrite !state_r34_nr_5F34.
  rewrite !state_r35_nr_5F35.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r34_nr_5F34 s)).
  rewrite ?(bits.mod_to_Z (N.r35_nr_5F35 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5255 (s : N.State) (i : N.Inputs) :
  R.v5255 (state s) (inputs i) = Zmod.unsigned (N.v5255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5255 s i)) at 1.
  unfold R.v5255, N.v5255.
  rewrite ?node_5225.
  rewrite !state_r36_nr_5F36.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r36_nr_5F36 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5256 (s : N.State) (i : N.Inputs) :
  R.v5256 (state s) (inputs i) = Zmod.unsigned (N.v5256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5256 s i)) at 1.
  unfold R.v5256, N.v5256.
  rewrite ?node_5254.
  rewrite ?node_5255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5257 (s : N.State) (i : N.Inputs) :
  R.v5257 (state s) (inputs i) = Zmod.unsigned (N.v5257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5257 s i)) at 1.
  unfold R.v5257, N.v5257.
  rewrite ?node_5253.
  rewrite ?node_5256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5258 (s : N.State) (i : N.Inputs) :
  R.v5258 (state s) (inputs i) = Zmod.unsigned (N.v5258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5258 s i)) at 1.
  unfold R.v5258, N.v5258.
  rewrite !state_r44_nr_5F44.
  rewrite !state_r45_nr_5F45.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r44_nr_5F44 s)).
  rewrite ?(bits.mod_to_Z (N.r45_nr_5F45 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5259 (s : N.State) (i : N.Inputs) :
  R.v5259 (state s) (inputs i) = Zmod.unsigned (N.v5259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5259 s i)) at 1.
  unfold R.v5259, N.v5259.
  rewrite ?node_5258.
  rewrite !state_r46_nr_5F46.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r46_nr_5F46 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5260 (s : N.State) (i : N.Inputs) :
  R.v5260 (state s) (inputs i) = Zmod.unsigned (N.v5260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5260 s i)) at 1.
  unfold R.v5260, N.v5260.
  rewrite ?node_5257.
  rewrite ?node_5259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5261 (s : N.State) (i : N.Inputs) :
  R.v5261 (state s) (inputs i) = Zmod.unsigned (N.v5261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5261 s i)) at 1.
  unfold R.v5261, N.v5261.
  rewrite ?node_5226.
  rewrite !state_r37_nr_5F37.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r37_nr_5F37 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5262 (s : N.State) (i : N.Inputs) :
  R.v5262 (state s) (inputs i) = Zmod.unsigned (N.v5262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5262 s i)) at 1.
  unfold R.v5262, N.v5262.
  rewrite ?node_5227.
  rewrite ?node_5230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5263 (s : N.State) (i : N.Inputs) :
  R.v5263 (state s) (inputs i) = Zmod.unsigned (N.v5263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5263 s i)) at 1.
  unfold R.v5263, N.v5263.
  rewrite ?node_5261.
  rewrite ?node_5262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5264 (s : N.State) (i : N.Inputs) :
  R.v5264 (state s) (inputs i) = Zmod.unsigned (N.v5264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5264 s i)) at 1.
  unfold R.v5264, N.v5264.
  rewrite ?node_5260.
  rewrite ?node_5263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5265 (s : N.State) (i : N.Inputs) :
  R.v5265 (state s) (inputs i) = Zmod.unsigned (N.v5265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5265 s i)) at 1.
  unfold R.v5265, N.v5265.
  rewrite !state_r38_nr_5F38.
  rewrite !state_r39_nr_5F39.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r38_nr_5F38 s)).
  rewrite ?(bits.mod_to_Z (N.r39_nr_5F39 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5266 (s : N.State) (i : N.Inputs) :
  R.v5266 (state s) (inputs i) = Zmod.unsigned (N.v5266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5266 s i)) at 1.
  unfold R.v5266, N.v5266.
  rewrite ?node_5264.
  rewrite ?node_5265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5267 (s : N.State) (i : N.Inputs) :
  R.v5267 (state s) (inputs i) = Zmod.unsigned (N.v5267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5267 s i)) at 1.
  unfold R.v5267, N.v5267.
  rewrite ?node_5231.
  rewrite ?node_5232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5268 (s : N.State) (i : N.Inputs) :
  R.v5268 (state s) (inputs i) = Zmod.unsigned (N.v5268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5268 s i)) at 1.
  unfold R.v5268, N.v5268.
  rewrite ?node_5233.
  rewrite ?node_5236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5269 (s : N.State) (i : N.Inputs) :
  R.v5269 (state s) (inputs i) = Zmod.unsigned (N.v5269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5269 s i)) at 1.
  unfold R.v5269, N.v5269.
  rewrite ?node_5267.
  rewrite ?node_5268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5270 (s : N.State) (i : N.Inputs) :
  R.v5270 (state s) (inputs i) = Zmod.unsigned (N.v5270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5270 s i)) at 1.
  unfold R.v5270, N.v5270.
  rewrite ?node_5266.
  rewrite ?node_5269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5271 (s : N.State) (i : N.Inputs) :
  R.v5271 (state s) (inputs i) = Zmod.unsigned (N.v5271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5271 s i)) at 1.
  unfold R.v5271, N.v5271.
  rewrite ?node_5237.
  rewrite ?node_5238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5272 (s : N.State) (i : N.Inputs) :
  R.v5272 (state s) (inputs i) = Zmod.unsigned (N.v5272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5272 s i)) at 1.
  unfold R.v5272, N.v5272.
  rewrite ?node_5270.
  rewrite ?node_5271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5273 (s : N.State) (i : N.Inputs) :
  R.v5273 (state s) (inputs i) = Zmod.unsigned (N.v5273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5273 s i)) at 1.
  unfold R.v5273, N.v5273.
  rewrite ?node_5239.
  rewrite ?node_5242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5274 (s : N.State) (i : N.Inputs) :
  R.v5274 (state s) (inputs i) = Zmod.unsigned (N.v5274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5274 s i)) at 1.
  unfold R.v5274, N.v5274.
  rewrite ?node_5272.
  rewrite ?node_5273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5275 (s : N.State) (i : N.Inputs) :
  R.v5275 (state s) (inputs i) = Zmod.unsigned (N.v5275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5275 s i)) at 1.
  unfold R.v5275, N.v5275.
  rewrite ?node_5243.
  rewrite ?node_5244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5276 (s : N.State) (i : N.Inputs) :
  R.v5276 (state s) (inputs i) = Zmod.unsigned (N.v5276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5276 s i)) at 1.
  unfold R.v5276, N.v5276.
  rewrite ?node_5274.
  rewrite ?node_5275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5277 (s : N.State) (i : N.Inputs) :
  R.v5277 (state s) (inputs i) = Zmod.unsigned (N.v5277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5277 s i)) at 1.
  unfold R.v5277, N.v5277.
  rewrite ?node_5276.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2293_nr_5F2324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2293_nr_5F2324 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5278 (s : N.State) (i : N.Inputs) :
  R.v5278 (state s) (inputs i) = Zmod.unsigned (N.v5278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5278 s i)) at 1.
  unfold R.v5278, N.v5278.
  rewrite ?node_5245.
  rewrite ?node_5246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5279 (s : N.State) (i : N.Inputs) :
  R.v5279 (state s) (inputs i) = Zmod.unsigned (N.v5279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5279 s i)) at 1.
  unfold R.v5279, N.v5279.
  rewrite ?node_5278.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2294_nr_5F2325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2294_nr_5F2325 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5280 (s : N.State) (i : N.Inputs) :
  R.v5280 (state s) (inputs i) = Zmod.unsigned (N.v5280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5280 s i)) at 1.
  unfold R.v5280, N.v5280.
  rewrite !state_r47_nr_5F47.
  rewrite !state_r48_nr_5F48.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r47_nr_5F47 s)).
  rewrite ?(bits.mod_to_Z (N.r48_nr_5F48 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5281 (s : N.State) (i : N.Inputs) :
  R.v5281 (state s) (inputs i) = Zmod.unsigned (N.v5281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5281 s i)) at 1.
  unfold R.v5281, N.v5281.
  rewrite ?node_5280.
  rewrite !state_r49_nr_5F49.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r49_nr_5F49 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5282 (s : N.State) (i : N.Inputs) :
  R.v5282 (state s) (inputs i) = Zmod.unsigned (N.v5282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5282 s i)) at 1.
  unfold R.v5282, N.v5282.
  rewrite ?node_5281.
  rewrite !state_r50_nr_5F50.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r50_nr_5F50 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5283 (s : N.State) (i : N.Inputs) :
  R.v5283 (state s) (inputs i) = Zmod.unsigned (N.v5283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5283 s i)) at 1.
  unfold R.v5283, N.v5283.
  rewrite !state_r40_nr_5F40.
  rewrite !state_r41_nr_5F41.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r40_nr_5F40 s)).
  rewrite ?(bits.mod_to_Z (N.r41_nr_5F41 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5284 (s : N.State) (i : N.Inputs) :
  R.v5284 (state s) (inputs i) = Zmod.unsigned (N.v5284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5284 s i)) at 1.
  unfold R.v5284, N.v5284.
  rewrite ?node_5251.
  rewrite !state_r42_nr_5F42.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r42_nr_5F42 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5285 (s : N.State) (i : N.Inputs) :
  R.v5285 (state s) (inputs i) = Zmod.unsigned (N.v5285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5285 s i)) at 1.
  unfold R.v5285, N.v5285.
  rewrite ?node_5283.
  rewrite ?node_5284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5286 (s : N.State) (i : N.Inputs) :
  R.v5286 (state s) (inputs i) = Zmod.unsigned (N.v5286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5286 s i)) at 1.
  unfold R.v5286, N.v5286.
  rewrite ?node_5282.
  rewrite ?node_5285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5287 (s : N.State) (i : N.Inputs) :
  R.v5287 (state s) (inputs i) = Zmod.unsigned (N.v5287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5287 s i)) at 1.
  unfold R.v5287, N.v5287.
  rewrite !state_r51_nr_5F51.
  rewrite !state_r52_nr_5F52.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r51_nr_5F51 s)).
  rewrite ?(bits.mod_to_Z (N.r52_nr_5F52 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5288 (s : N.State) (i : N.Inputs) :
  R.v5288 (state s) (inputs i) = Zmod.unsigned (N.v5288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5288 s i)) at 1.
  unfold R.v5288, N.v5288.
  rewrite ?node_5287.
  rewrite !state_r53_nr_5F53.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r53_nr_5F53 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5289 (s : N.State) (i : N.Inputs) :
  R.v5289 (state s) (inputs i) = Zmod.unsigned (N.v5289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5289 s i)) at 1.
  unfold R.v5289, N.v5289.
  rewrite ?node_5286.
  rewrite ?node_5288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5290 (s : N.State) (i : N.Inputs) :
  R.v5290 (state s) (inputs i) = Zmod.unsigned (N.v5290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5290 s i)) at 1.
  unfold R.v5290, N.v5290.
  rewrite ?node_5252.
  rewrite !state_r43_nr_5F43.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r43_nr_5F43 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5291 (s : N.State) (i : N.Inputs) :
  R.v5291 (state s) (inputs i) = Zmod.unsigned (N.v5291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5291 s i)) at 1.
  unfold R.v5291, N.v5291.
  rewrite ?node_5253.
  rewrite ?node_5256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5292 (s : N.State) (i : N.Inputs) :
  R.v5292 (state s) (inputs i) = Zmod.unsigned (N.v5292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5292 s i)) at 1.
  unfold R.v5292, N.v5292.
  rewrite ?node_5290.
  rewrite ?node_5291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5293 (s : N.State) (i : N.Inputs) :
  R.v5293 (state s) (inputs i) = Zmod.unsigned (N.v5293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5293 s i)) at 1.
  unfold R.v5293, N.v5293.
  rewrite ?node_5289.
  rewrite ?node_5292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5294 (s : N.State) (i : N.Inputs) :
  R.v5294 (state s) (inputs i) = Zmod.unsigned (N.v5294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5294 s i)) at 1.
  unfold R.v5294, N.v5294.
  rewrite !state_r44_nr_5F44.
  rewrite !state_r45_nr_5F45.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r44_nr_5F44 s)).
  rewrite ?(bits.mod_to_Z (N.r45_nr_5F45 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5295 (s : N.State) (i : N.Inputs) :
  R.v5295 (state s) (inputs i) = Zmod.unsigned (N.v5295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5295 s i)) at 1.
  unfold R.v5295, N.v5295.
  rewrite ?node_5258.
  rewrite !state_r46_nr_5F46.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r46_nr_5F46 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5296 (s : N.State) (i : N.Inputs) :
  R.v5296 (state s) (inputs i) = Zmod.unsigned (N.v5296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5296 s i)) at 1.
  unfold R.v5296, N.v5296.
  rewrite ?node_5294.
  rewrite ?node_5295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5297 (s : N.State) (i : N.Inputs) :
  R.v5297 (state s) (inputs i) = Zmod.unsigned (N.v5297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5297 s i)) at 1.
  unfold R.v5297, N.v5297.
  rewrite ?node_5293.
  rewrite ?node_5296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5298 (s : N.State) (i : N.Inputs) :
  R.v5298 (state s) (inputs i) = Zmod.unsigned (N.v5298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5298 s i)) at 1.
  unfold R.v5298, N.v5298.
  rewrite ?node_5257.
  rewrite ?node_5259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5299 (s : N.State) (i : N.Inputs) :
  R.v5299 (state s) (inputs i) = Zmod.unsigned (N.v5299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5299 s i)) at 1.
  unfold R.v5299, N.v5299.
  rewrite ?node_5260.
  rewrite ?node_5263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5300 (s : N.State) (i : N.Inputs) :
  R.v5300 (state s) (inputs i) = Zmod.unsigned (N.v5300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5300 s i)) at 1.
  unfold R.v5300, N.v5300.
  rewrite ?node_5298.
  rewrite ?node_5299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5301 (s : N.State) (i : N.Inputs) :
  R.v5301 (state s) (inputs i) = Zmod.unsigned (N.v5301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5301 s i)) at 1.
  unfold R.v5301, N.v5301.
  rewrite ?node_5297.
  rewrite ?node_5300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5302 (s : N.State) (i : N.Inputs) :
  R.v5302 (state s) (inputs i) = Zmod.unsigned (N.v5302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5302 s i)) at 1.
  unfold R.v5302, N.v5302.
  rewrite ?node_5264.
  rewrite ?node_5265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5303 (s : N.State) (i : N.Inputs) :
  R.v5303 (state s) (inputs i) = Zmod.unsigned (N.v5303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5303 s i)) at 1.
  unfold R.v5303, N.v5303.
  rewrite ?node_5266.
  rewrite ?node_5269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5304 (s : N.State) (i : N.Inputs) :
  R.v5304 (state s) (inputs i) = Zmod.unsigned (N.v5304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5304 s i)) at 1.
  unfold R.v5304, N.v5304.
  rewrite ?node_5302.
  rewrite ?node_5303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5305 (s : N.State) (i : N.Inputs) :
  R.v5305 (state s) (inputs i) = Zmod.unsigned (N.v5305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5305 s i)) at 1.
  unfold R.v5305, N.v5305.
  rewrite ?node_5301.
  rewrite ?node_5304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5306 (s : N.State) (i : N.Inputs) :
  R.v5306 (state s) (inputs i) = Zmod.unsigned (N.v5306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5306 s i)) at 1.
  unfold R.v5306, N.v5306.
  rewrite ?node_5270.
  rewrite ?node_5271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5307 (s : N.State) (i : N.Inputs) :
  R.v5307 (state s) (inputs i) = Zmod.unsigned (N.v5307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5307 s i)) at 1.
  unfold R.v5307, N.v5307.
  rewrite ?node_5305.
  rewrite ?node_5306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5308 (s : N.State) (i : N.Inputs) :
  R.v5308 (state s) (inputs i) = Zmod.unsigned (N.v5308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5308 s i)) at 1.
  unfold R.v5308, N.v5308.
  rewrite ?node_5272.
  rewrite ?node_5273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5309 (s : N.State) (i : N.Inputs) :
  R.v5309 (state s) (inputs i) = Zmod.unsigned (N.v5309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5309 s i)) at 1.
  unfold R.v5309, N.v5309.
  rewrite ?node_5307.
  rewrite ?node_5308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5310 (s : N.State) (i : N.Inputs) :
  R.v5310 (state s) (inputs i) = Zmod.unsigned (N.v5310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5310 s i)) at 1.
  unfold R.v5310, N.v5310.
  rewrite ?node_5309.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2295_nr_5F2326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2295_nr_5F2326 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5311 (s : N.State) (i : N.Inputs) :
  R.v5311 (state s) (inputs i) = Zmod.unsigned (N.v5311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5311 s i)) at 1.
  unfold R.v5311, N.v5311.
  rewrite ?node_5274.
  rewrite ?node_5275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5312 (s : N.State) (i : N.Inputs) :
  R.v5312 (state s) (inputs i) = Zmod.unsigned (N.v5312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5312 s i)) at 1.
  unfold R.v5312, N.v5312.
  rewrite ?node_5311.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2296_nr_5F2327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2296_nr_5F2327 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5313 (s : N.State) (i : N.Inputs) :
  R.v5313 (state s) (inputs i) = Zmod.unsigned (N.v5313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5313 s i)) at 1.
  unfold R.v5313, N.v5313.
  rewrite !state_r54_nr_5F54.
  rewrite !state_r55_nr_5F55.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r54_nr_5F54 s)).
  rewrite ?(bits.mod_to_Z (N.r55_nr_5F55 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5314 (s : N.State) (i : N.Inputs) :
  R.v5314 (state s) (inputs i) = Zmod.unsigned (N.v5314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5314 s i)) at 1.
  unfold R.v5314, N.v5314.
  rewrite ?node_5313.
  rewrite !state_r56_nr_5F56.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r56_nr_5F56 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5315 (s : N.State) (i : N.Inputs) :
  R.v5315 (state s) (inputs i) = Zmod.unsigned (N.v5315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5315 s i)) at 1.
  unfold R.v5315, N.v5315.
  rewrite ?node_5314.
  rewrite !state_r57_nr_5F57.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r57_nr_5F57 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5316 (s : N.State) (i : N.Inputs) :
  R.v5316 (state s) (inputs i) = Zmod.unsigned (N.v5316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5316 s i)) at 1.
  unfold R.v5316, N.v5316.
  rewrite !state_r47_nr_5F47.
  rewrite !state_r48_nr_5F48.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r47_nr_5F47 s)).
  rewrite ?(bits.mod_to_Z (N.r48_nr_5F48 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5317 (s : N.State) (i : N.Inputs) :
  R.v5317 (state s) (inputs i) = Zmod.unsigned (N.v5317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5317 s i)) at 1.
  unfold R.v5317, N.v5317.
  rewrite ?node_5280.
  rewrite !state_r49_nr_5F49.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r49_nr_5F49 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5318 (s : N.State) (i : N.Inputs) :
  R.v5318 (state s) (inputs i) = Zmod.unsigned (N.v5318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5318 s i)) at 1.
  unfold R.v5318, N.v5318.
  rewrite ?node_5316.
  rewrite ?node_5317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5319 (s : N.State) (i : N.Inputs) :
  R.v5319 (state s) (inputs i) = Zmod.unsigned (N.v5319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5319 s i)) at 1.
  unfold R.v5319, N.v5319.
  rewrite ?node_5315.
  rewrite ?node_5318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5320 (s : N.State) (i : N.Inputs) :
  R.v5320 (state s) (inputs i) = Zmod.unsigned (N.v5320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5320 s i)) at 1.
  unfold R.v5320, N.v5320.
  rewrite !state_r58_nr_5F58.
  rewrite !state_r59_nr_5F59.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r58_nr_5F58 s)).
  rewrite ?(bits.mod_to_Z (N.r59_nr_5F59 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5321 (s : N.State) (i : N.Inputs) :
  R.v5321 (state s) (inputs i) = Zmod.unsigned (N.v5321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5321 s i)) at 1.
  unfold R.v5321, N.v5321.
  rewrite ?node_5320.
  rewrite !state_r60_nr_5F60.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r60_nr_5F60 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5322 (s : N.State) (i : N.Inputs) :
  R.v5322 (state s) (inputs i) = Zmod.unsigned (N.v5322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5322 s i)) at 1.
  unfold R.v5322, N.v5322.
  rewrite ?node_5321.
  rewrite !state_r61_nr_5F61.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r61_nr_5F61 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5323 (s : N.State) (i : N.Inputs) :
  R.v5323 (state s) (inputs i) = Zmod.unsigned (N.v5323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5323 s i)) at 1.
  unfold R.v5323, N.v5323.
  rewrite ?node_5319.
  rewrite ?node_5322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5324 (s : N.State) (i : N.Inputs) :
  R.v5324 (state s) (inputs i) = Zmod.unsigned (N.v5324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5324 s i)) at 1.
  unfold R.v5324, N.v5324.
  rewrite ?node_5281.
  rewrite !state_r50_nr_5F50.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r50_nr_5F50 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5325 (s : N.State) (i : N.Inputs) :
  R.v5325 (state s) (inputs i) = Zmod.unsigned (N.v5325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5325 s i)) at 1.
  unfold R.v5325, N.v5325.
  rewrite ?node_5282.
  rewrite ?node_5285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5326 (s : N.State) (i : N.Inputs) :
  R.v5326 (state s) (inputs i) = Zmod.unsigned (N.v5326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5326 s i)) at 1.
  unfold R.v5326, N.v5326.
  rewrite ?node_5324.
  rewrite ?node_5325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5327 (s : N.State) (i : N.Inputs) :
  R.v5327 (state s) (inputs i) = Zmod.unsigned (N.v5327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5327 s i)) at 1.
  unfold R.v5327, N.v5327.
  rewrite ?node_5323.
  rewrite ?node_5326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5328 (s : N.State) (i : N.Inputs) :
  R.v5328 (state s) (inputs i) = Zmod.unsigned (N.v5328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5328 s i)) at 1.
  unfold R.v5328, N.v5328.
  rewrite !state_r51_nr_5F51.
  rewrite !state_r52_nr_5F52.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r51_nr_5F51 s)).
  rewrite ?(bits.mod_to_Z (N.r52_nr_5F52 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5329 (s : N.State) (i : N.Inputs) :
  R.v5329 (state s) (inputs i) = Zmod.unsigned (N.v5329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5329 s i)) at 1.
  unfold R.v5329, N.v5329.
  rewrite ?node_5287.
  rewrite !state_r53_nr_5F53.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r53_nr_5F53 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5330 (s : N.State) (i : N.Inputs) :
  R.v5330 (state s) (inputs i) = Zmod.unsigned (N.v5330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5330 s i)) at 1.
  unfold R.v5330, N.v5330.
  rewrite ?node_5328.
  rewrite ?node_5329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5331 (s : N.State) (i : N.Inputs) :
  R.v5331 (state s) (inputs i) = Zmod.unsigned (N.v5331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5331 s i)) at 1.
  unfold R.v5331, N.v5331.
  rewrite ?node_5327.
  rewrite ?node_5330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5332 (s : N.State) (i : N.Inputs) :
  R.v5332 (state s) (inputs i) = Zmod.unsigned (N.v5332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5332 s i)) at 1.
  unfold R.v5332, N.v5332.
  rewrite ?node_5286.
  rewrite ?node_5288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5333 (s : N.State) (i : N.Inputs) :
  R.v5333 (state s) (inputs i) = Zmod.unsigned (N.v5333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5333 s i)) at 1.
  unfold R.v5333, N.v5333.
  rewrite ?node_5289.
  rewrite ?node_5292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5334 (s : N.State) (i : N.Inputs) :
  R.v5334 (state s) (inputs i) = Zmod.unsigned (N.v5334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5334 s i)) at 1.
  unfold R.v5334, N.v5334.
  rewrite ?node_5332.
  rewrite ?node_5333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5335 (s : N.State) (i : N.Inputs) :
  R.v5335 (state s) (inputs i) = Zmod.unsigned (N.v5335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5335 s i)) at 1.
  unfold R.v5335, N.v5335.
  rewrite ?node_5331.
  rewrite ?node_5334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5336 (s : N.State) (i : N.Inputs) :
  R.v5336 (state s) (inputs i) = Zmod.unsigned (N.v5336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5336 s i)) at 1.
  unfold R.v5336, N.v5336.
  rewrite ?node_5293.
  rewrite ?node_5296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5337 (s : N.State) (i : N.Inputs) :
  R.v5337 (state s) (inputs i) = Zmod.unsigned (N.v5337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5337 s i)) at 1.
  unfold R.v5337, N.v5337.
  rewrite ?node_5297.
  rewrite ?node_5300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5338 (s : N.State) (i : N.Inputs) :
  R.v5338 (state s) (inputs i) = Zmod.unsigned (N.v5338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5338 s i)) at 1.
  unfold R.v5338, N.v5338.
  rewrite ?node_5336.
  rewrite ?node_5337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5339 (s : N.State) (i : N.Inputs) :
  R.v5339 (state s) (inputs i) = Zmod.unsigned (N.v5339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5339 s i)) at 1.
  unfold R.v5339, N.v5339.
  rewrite ?node_5335.
  rewrite ?node_5338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5340 (s : N.State) (i : N.Inputs) :
  R.v5340 (state s) (inputs i) = Zmod.unsigned (N.v5340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5340 s i)) at 1.
  unfold R.v5340, N.v5340.
  rewrite ?node_5301.
  rewrite ?node_5304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5341 (s : N.State) (i : N.Inputs) :
  R.v5341 (state s) (inputs i) = Zmod.unsigned (N.v5341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5341 s i)) at 1.
  unfold R.v5341, N.v5341.
  rewrite ?node_5339.
  rewrite ?node_5340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5342 (s : N.State) (i : N.Inputs) :
  R.v5342 (state s) (inputs i) = Zmod.unsigned (N.v5342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5342 s i)) at 1.
  unfold R.v5342, N.v5342.
  rewrite ?node_5305.
  rewrite ?node_5306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5343 (s : N.State) (i : N.Inputs) :
  R.v5343 (state s) (inputs i) = Zmod.unsigned (N.v5343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5343 s i)) at 1.
  unfold R.v5343, N.v5343.
  rewrite ?node_5341.
  rewrite ?node_5342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5344 (s : N.State) (i : N.Inputs) :
  R.v5344 (state s) (inputs i) = Zmod.unsigned (N.v5344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5344 s i)) at 1.
  unfold R.v5344, N.v5344.
  rewrite ?node_5343.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2297_nr_5F2328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2297_nr_5F2328 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5345 (s : N.State) (i : N.Inputs) :
  R.v5345 (state s) (inputs i) = Zmod.unsigned (N.v5345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5345 s i)) at 1.
  unfold R.v5345, N.v5345.
  rewrite ?node_5307.
  rewrite ?node_5308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5346 (s : N.State) (i : N.Inputs) :
  R.v5346 (state s) (inputs i) = Zmod.unsigned (N.v5346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5346 s i)) at 1.
  unfold R.v5346, N.v5346.
  rewrite ?node_5345.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2298_nr_5F2329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2298_nr_5F2329 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5347 (s : N.State) (i : N.Inputs) :
  R.v5347 (state s) (inputs i) = Zmod.unsigned (N.v5347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5347 s i)) at 1.
  unfold R.v5347, N.v5347.
  rewrite !state_r62_nr_5F62.
  rewrite !state_r63_nr_5F63.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r62_nr_5F62 s)).
  rewrite ?(bits.mod_to_Z (N.r63_nr_5F63 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5348 (s : N.State) (i : N.Inputs) :
  R.v5348 (state s) (inputs i) = Zmod.unsigned (N.v5348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5348 s i)) at 1.
  unfold R.v5348, N.v5348.
  rewrite ?node_5347.
  rewrite !state_r64_nr_5F64.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r64_nr_5F64 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5349 (s : N.State) (i : N.Inputs) :
  R.v5349 (state s) (inputs i) = Zmod.unsigned (N.v5349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5349 s i)) at 1.
  unfold R.v5349, N.v5349.
  rewrite ?node_5348.
  rewrite !state_r65_nr_5F65.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r65_nr_5F65 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5350 (s : N.State) (i : N.Inputs) :
  R.v5350 (state s) (inputs i) = Zmod.unsigned (N.v5350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5350 s i)) at 1.
  unfold R.v5350, N.v5350.
  rewrite !state_r54_nr_5F54.
  rewrite !state_r55_nr_5F55.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r54_nr_5F54 s)).
  rewrite ?(bits.mod_to_Z (N.r55_nr_5F55 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5351 (s : N.State) (i : N.Inputs) :
  R.v5351 (state s) (inputs i) = Zmod.unsigned (N.v5351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5351 s i)) at 1.
  unfold R.v5351, N.v5351.
  rewrite ?node_5313.
  rewrite !state_r56_nr_5F56.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r56_nr_5F56 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5352 (s : N.State) (i : N.Inputs) :
  R.v5352 (state s) (inputs i) = Zmod.unsigned (N.v5352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5352 s i)) at 1.
  unfold R.v5352, N.v5352.
  rewrite ?node_5350.
  rewrite ?node_5351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5353 (s : N.State) (i : N.Inputs) :
  R.v5353 (state s) (inputs i) = Zmod.unsigned (N.v5353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5353 s i)) at 1.
  unfold R.v5353, N.v5353.
  rewrite ?node_5349.
  rewrite ?node_5352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5354 (s : N.State) (i : N.Inputs) :
  R.v5354 (state s) (inputs i) = Zmod.unsigned (N.v5354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5354 s i)) at 1.
  unfold R.v5354, N.v5354.
  rewrite !state_r66_nr_5F66.
  rewrite !state_r67_nr_5F67.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r66_nr_5F66 s)).
  rewrite ?(bits.mod_to_Z (N.r67_nr_5F67 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5355 (s : N.State) (i : N.Inputs) :
  R.v5355 (state s) (inputs i) = Zmod.unsigned (N.v5355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5355 s i)) at 1.
  unfold R.v5355, N.v5355.
  rewrite ?node_5354.
  rewrite !state_r68_nr_5F68.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r68_nr_5F68 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5356 (s : N.State) (i : N.Inputs) :
  R.v5356 (state s) (inputs i) = Zmod.unsigned (N.v5356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5356 s i)) at 1.
  unfold R.v5356, N.v5356.
  rewrite ?node_5355.
  rewrite !state_r69_nr_5F69.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r69_nr_5F69 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5357 (s : N.State) (i : N.Inputs) :
  R.v5357 (state s) (inputs i) = Zmod.unsigned (N.v5357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5357 s i)) at 1.
  unfold R.v5357, N.v5357.
  rewrite !state_r58_nr_5F58.
  rewrite !state_r59_nr_5F59.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r58_nr_5F58 s)).
  rewrite ?(bits.mod_to_Z (N.r59_nr_5F59 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5358 (s : N.State) (i : N.Inputs) :
  R.v5358 (state s) (inputs i) = Zmod.unsigned (N.v5358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5358 s i)) at 1.
  unfold R.v5358, N.v5358.
  rewrite ?node_5320.
  rewrite !state_r60_nr_5F60.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r60_nr_5F60 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5359 (s : N.State) (i : N.Inputs) :
  R.v5359 (state s) (inputs i) = Zmod.unsigned (N.v5359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5359 s i)) at 1.
  unfold R.v5359, N.v5359.
  rewrite ?node_5357.
  rewrite ?node_5358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5360 (s : N.State) (i : N.Inputs) :
  R.v5360 (state s) (inputs i) = Zmod.unsigned (N.v5360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5360 s i)) at 1.
  unfold R.v5360, N.v5360.
  rewrite ?node_5356.
  rewrite ?node_5359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5361 (s : N.State) (i : N.Inputs) :
  R.v5361 (state s) (inputs i) = Zmod.unsigned (N.v5361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5361 s i)) at 1.
  unfold R.v5361, N.v5361.
  rewrite ?node_5353.
  rewrite ?node_5360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5362 (s : N.State) (i : N.Inputs) :
  R.v5362 (state s) (inputs i) = Zmod.unsigned (N.v5362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5362 s i)) at 1.
  unfold R.v5362, N.v5362.
  rewrite ?node_5314.
  rewrite !state_r57_nr_5F57.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r57_nr_5F57 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5363 (s : N.State) (i : N.Inputs) :
  R.v5363 (state s) (inputs i) = Zmod.unsigned (N.v5363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5363 s i)) at 1.
  unfold R.v5363, N.v5363.
  rewrite ?node_5315.
  rewrite ?node_5318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5364 (s : N.State) (i : N.Inputs) :
  R.v5364 (state s) (inputs i) = Zmod.unsigned (N.v5364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5364 s i)) at 1.
  unfold R.v5364, N.v5364.
  rewrite ?node_5362.
  rewrite ?node_5363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5365 (s : N.State) (i : N.Inputs) :
  R.v5365 (state s) (inputs i) = Zmod.unsigned (N.v5365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5365 s i)) at 1.
  unfold R.v5365, N.v5365.
  rewrite ?node_5361.
  rewrite ?node_5364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5366 (s : N.State) (i : N.Inputs) :
  R.v5366 (state s) (inputs i) = Zmod.unsigned (N.v5366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5366 s i)) at 1.
  unfold R.v5366, N.v5366.
  rewrite ?node_5321.
  rewrite !state_r61_nr_5F61.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r61_nr_5F61 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5367 (s : N.State) (i : N.Inputs) :
  R.v5367 (state s) (inputs i) = Zmod.unsigned (N.v5367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5367 s i)) at 1.
  unfold R.v5367, N.v5367.
  rewrite ?node_5365.
  rewrite ?node_5366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5368 (s : N.State) (i : N.Inputs) :
  R.v5368 (state s) (inputs i) = Zmod.unsigned (N.v5368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5368 s i)) at 1.
  unfold R.v5368, N.v5368.
  rewrite ?node_5319.
  rewrite ?node_5322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5369 (s : N.State) (i : N.Inputs) :
  R.v5369 (state s) (inputs i) = Zmod.unsigned (N.v5369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5369 s i)) at 1.
  unfold R.v5369, N.v5369.
  rewrite ?node_5323.
  rewrite ?node_5326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5370 (s : N.State) (i : N.Inputs) :
  R.v5370 (state s) (inputs i) = Zmod.unsigned (N.v5370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5370 s i)) at 1.
  unfold R.v5370, N.v5370.
  rewrite ?node_5368.
  rewrite ?node_5369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5371 (s : N.State) (i : N.Inputs) :
  R.v5371 (state s) (inputs i) = Zmod.unsigned (N.v5371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5371 s i)) at 1.
  unfold R.v5371, N.v5371.
  rewrite ?node_5367.
  rewrite ?node_5370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5372 (s : N.State) (i : N.Inputs) :
  R.v5372 (state s) (inputs i) = Zmod.unsigned (N.v5372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5372 s i)) at 1.
  unfold R.v5372, N.v5372.
  rewrite ?node_5327.
  rewrite ?node_5330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5373 (s : N.State) (i : N.Inputs) :
  R.v5373 (state s) (inputs i) = Zmod.unsigned (N.v5373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5373 s i)) at 1.
  unfold R.v5373, N.v5373.
  rewrite ?node_5331.
  rewrite ?node_5334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5374 (s : N.State) (i : N.Inputs) :
  R.v5374 (state s) (inputs i) = Zmod.unsigned (N.v5374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5374 s i)) at 1.
  unfold R.v5374, N.v5374.
  rewrite ?node_5372.
  rewrite ?node_5373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5375 (s : N.State) (i : N.Inputs) :
  R.v5375 (state s) (inputs i) = Zmod.unsigned (N.v5375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5375 s i)) at 1.
  unfold R.v5375, N.v5375.
  rewrite ?node_5371.
  rewrite ?node_5374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5376 (s : N.State) (i : N.Inputs) :
  R.v5376 (state s) (inputs i) = Zmod.unsigned (N.v5376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5376 s i)) at 1.
  unfold R.v5376, N.v5376.
  rewrite ?node_5335.
  rewrite ?node_5338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5377 (s : N.State) (i : N.Inputs) :
  R.v5377 (state s) (inputs i) = Zmod.unsigned (N.v5377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5377 s i)) at 1.
  unfold R.v5377, N.v5377.
  rewrite ?node_5375.
  rewrite ?node_5376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5378 (s : N.State) (i : N.Inputs) :
  R.v5378 (state s) (inputs i) = Zmod.unsigned (N.v5378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5378 s i)) at 1.
  unfold R.v5378, N.v5378.
  rewrite ?node_5339.
  rewrite ?node_5340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5379 (s : N.State) (i : N.Inputs) :
  R.v5379 (state s) (inputs i) = Zmod.unsigned (N.v5379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5379 s i)) at 1.
  unfold R.v5379, N.v5379.
  rewrite ?node_5377.
  rewrite ?node_5378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5380 (s : N.State) (i : N.Inputs) :
  R.v5380 (state s) (inputs i) = Zmod.unsigned (N.v5380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5380 s i)) at 1.
  unfold R.v5380, N.v5380.
  rewrite ?node_5379.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2299_nr_5F2330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2299_nr_5F2330 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5381 (s : N.State) (i : N.Inputs) :
  R.v5381 (state s) (inputs i) = Zmod.unsigned (N.v5381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5381 s i)) at 1.
  unfold R.v5381, N.v5381.
  rewrite ?node_5341.
  rewrite ?node_5342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5382 (s : N.State) (i : N.Inputs) :
  R.v5382 (state s) (inputs i) = Zmod.unsigned (N.v5382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5382 s i)) at 1.
  unfold R.v5382, N.v5382.
  rewrite ?node_5381.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2300_nr_5F2331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2300_nr_5F2331 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5383 (s : N.State) (i : N.Inputs) :
  R.v5383 (state s) (inputs i) = Zmod.unsigned (N.v5383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5383 s i)) at 1.
  unfold R.v5383, N.v5383.
  rewrite !state_r70_nr_5F70.
  rewrite !state_r71_nr_5F71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r70_nr_5F70 s)).
  rewrite ?(bits.mod_to_Z (N.r71_nr_5F71 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5384 (s : N.State) (i : N.Inputs) :
  R.v5384 (state s) (inputs i) = Zmod.unsigned (N.v5384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5384 s i)) at 1.
  unfold R.v5384, N.v5384.
  rewrite ?node_5383.
  rewrite !state_r72_nr_5F72.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r72_nr_5F72 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5385 (s : N.State) (i : N.Inputs) :
  R.v5385 (state s) (inputs i) = Zmod.unsigned (N.v5385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5385 s i)) at 1.
  unfold R.v5385, N.v5385.
  rewrite ?node_5384.
  rewrite !state_r73_nr_5F73.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r73_nr_5F73 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5386 (s : N.State) (i : N.Inputs) :
  R.v5386 (state s) (inputs i) = Zmod.unsigned (N.v5386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5386 s i)) at 1.
  unfold R.v5386, N.v5386.
  rewrite !state_r62_nr_5F62.
  rewrite !state_r63_nr_5F63.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r62_nr_5F62 s)).
  rewrite ?(bits.mod_to_Z (N.r63_nr_5F63 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5387 (s : N.State) (i : N.Inputs) :
  R.v5387 (state s) (inputs i) = Zmod.unsigned (N.v5387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5387 s i)) at 1.
  unfold R.v5387, N.v5387.
  rewrite ?node_5347.
  rewrite !state_r64_nr_5F64.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r64_nr_5F64 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5388 (s : N.State) (i : N.Inputs) :
  R.v5388 (state s) (inputs i) = Zmod.unsigned (N.v5388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5388 s i)) at 1.
  unfold R.v5388, N.v5388.
  rewrite ?node_5386.
  rewrite ?node_5387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5389 (s : N.State) (i : N.Inputs) :
  R.v5389 (state s) (inputs i) = Zmod.unsigned (N.v5389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5389 s i)) at 1.
  unfold R.v5389, N.v5389.
  rewrite ?node_5385.
  rewrite ?node_5388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5390 (s : N.State) (i : N.Inputs) :
  R.v5390 (state s) (inputs i) = Zmod.unsigned (N.v5390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5390 s i)) at 1.
  unfold R.v5390, N.v5390.
  rewrite !state_r74_nr_5F74.
  rewrite !state_r75_nr_5F75.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r74_nr_5F74 s)).
  rewrite ?(bits.mod_to_Z (N.r75_nr_5F75 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5391 (s : N.State) (i : N.Inputs) :
  R.v5391 (state s) (inputs i) = Zmod.unsigned (N.v5391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5391 s i)) at 1.
  unfold R.v5391, N.v5391.
  rewrite ?node_5390.
  rewrite !state_r76_nr_5F76.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r76_nr_5F76 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5392 (s : N.State) (i : N.Inputs) :
  R.v5392 (state s) (inputs i) = Zmod.unsigned (N.v5392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5392 s i)) at 1.
  unfold R.v5392, N.v5392.
  rewrite ?node_5391.
  rewrite !state_r77_nr_5F77.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r77_nr_5F77 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5393 (s : N.State) (i : N.Inputs) :
  R.v5393 (state s) (inputs i) = Zmod.unsigned (N.v5393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5393 s i)) at 1.
  unfold R.v5393, N.v5393.
  rewrite !state_r66_nr_5F66.
  rewrite !state_r67_nr_5F67.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r66_nr_5F66 s)).
  rewrite ?(bits.mod_to_Z (N.r67_nr_5F67 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5394 (s : N.State) (i : N.Inputs) :
  R.v5394 (state s) (inputs i) = Zmod.unsigned (N.v5394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5394 s i)) at 1.
  unfold R.v5394, N.v5394.
  rewrite ?node_5354.
  rewrite !state_r68_nr_5F68.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r68_nr_5F68 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5395 (s : N.State) (i : N.Inputs) :
  R.v5395 (state s) (inputs i) = Zmod.unsigned (N.v5395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5395 s i)) at 1.
  unfold R.v5395, N.v5395.
  rewrite ?node_5393.
  rewrite ?node_5394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5396 (s : N.State) (i : N.Inputs) :
  R.v5396 (state s) (inputs i) = Zmod.unsigned (N.v5396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5396 s i)) at 1.
  unfold R.v5396, N.v5396.
  rewrite ?node_5392.
  rewrite ?node_5395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5397 (s : N.State) (i : N.Inputs) :
  R.v5397 (state s) (inputs i) = Zmod.unsigned (N.v5397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5397 s i)) at 1.
  unfold R.v5397, N.v5397.
  rewrite ?node_5389.
  rewrite ?node_5396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5398 (s : N.State) (i : N.Inputs) :
  R.v5398 (state s) (inputs i) = Zmod.unsigned (N.v5398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5398 s i)) at 1.
  unfold R.v5398, N.v5398.
  rewrite ?node_5397.
  rewrite !state_r78_nr_5F78.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r78_nr_5F78 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5399 (s : N.State) (i : N.Inputs) :
  R.v5399 (state s) (inputs i) = Zmod.unsigned (N.v5399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5399 s i)) at 1.
  unfold R.v5399, N.v5399.
  rewrite ?node_5348.
  rewrite !state_r65_nr_5F65.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r65_nr_5F65 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5400 (s : N.State) (i : N.Inputs) :
  R.v5400 (state s) (inputs i) = Zmod.unsigned (N.v5400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5400 s i)) at 1.
  unfold R.v5400, N.v5400.
  rewrite ?node_5349.
  rewrite ?node_5352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5401 (s : N.State) (i : N.Inputs) :
  R.v5401 (state s) (inputs i) = Zmod.unsigned (N.v5401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5401 s i)) at 1.
  unfold R.v5401, N.v5401.
  rewrite ?node_5399.
  rewrite ?node_5400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5402 (s : N.State) (i : N.Inputs) :
  R.v5402 (state s) (inputs i) = Zmod.unsigned (N.v5402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5402 s i)) at 1.
  unfold R.v5402, N.v5402.
  rewrite ?node_5398.
  rewrite ?node_5401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5403 (s : N.State) (i : N.Inputs) :
  R.v5403 (state s) (inputs i) = Zmod.unsigned (N.v5403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5403 s i)) at 1.
  unfold R.v5403, N.v5403.
  rewrite ?node_5353.
  rewrite ?node_5360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5404 (s : N.State) (i : N.Inputs) :
  R.v5404 (state s) (inputs i) = Zmod.unsigned (N.v5404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5404 s i)) at 1.
  unfold R.v5404, N.v5404.
  rewrite ?node_5361.
  rewrite ?node_5364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5405 (s : N.State) (i : N.Inputs) :
  R.v5405 (state s) (inputs i) = Zmod.unsigned (N.v5405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5405 s i)) at 1.
  unfold R.v5405, N.v5405.
  rewrite ?node_5403.
  rewrite ?node_5404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5406 (s : N.State) (i : N.Inputs) :
  R.v5406 (state s) (inputs i) = Zmod.unsigned (N.v5406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5406 s i)) at 1.
  unfold R.v5406, N.v5406.
  rewrite ?node_5402.
  rewrite ?node_5405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5407 (s : N.State) (i : N.Inputs) :
  R.v5407 (state s) (inputs i) = Zmod.unsigned (N.v5407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5407 s i)) at 1.
  unfold R.v5407, N.v5407.
  rewrite ?node_5355.
  rewrite !state_r69_nr_5F69.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r69_nr_5F69 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5408 (s : N.State) (i : N.Inputs) :
  R.v5408 (state s) (inputs i) = Zmod.unsigned (N.v5408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5408 s i)) at 1.
  unfold R.v5408, N.v5408.
  rewrite ?node_5356.
  rewrite ?node_5359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5409 (s : N.State) (i : N.Inputs) :
  R.v5409 (state s) (inputs i) = Zmod.unsigned (N.v5409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5409 s i)) at 1.
  unfold R.v5409, N.v5409.
  rewrite ?node_5407.
  rewrite ?node_5408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5410 (s : N.State) (i : N.Inputs) :
  R.v5410 (state s) (inputs i) = Zmod.unsigned (N.v5410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5410 s i)) at 1.
  unfold R.v5410, N.v5410.
  rewrite ?node_5406.
  rewrite ?node_5409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5411 (s : N.State) (i : N.Inputs) :
  R.v5411 (state s) (inputs i) = Zmod.unsigned (N.v5411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5411 s i)) at 1.
  unfold R.v5411, N.v5411.
  rewrite ?node_5365.
  rewrite ?node_5366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5412 (s : N.State) (i : N.Inputs) :
  R.v5412 (state s) (inputs i) = Zmod.unsigned (N.v5412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5412 s i)) at 1.
  unfold R.v5412, N.v5412.
  rewrite ?node_5367.
  rewrite ?node_5370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5413 (s : N.State) (i : N.Inputs) :
  R.v5413 (state s) (inputs i) = Zmod.unsigned (N.v5413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5413 s i)) at 1.
  unfold R.v5413, N.v5413.
  rewrite ?node_5411.
  rewrite ?node_5412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5414 (s : N.State) (i : N.Inputs) :
  R.v5414 (state s) (inputs i) = Zmod.unsigned (N.v5414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5414 s i)) at 1.
  unfold R.v5414, N.v5414.
  rewrite ?node_5410.
  rewrite ?node_5413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5415 (s : N.State) (i : N.Inputs) :
  R.v5415 (state s) (inputs i) = Zmod.unsigned (N.v5415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5415 s i)) at 1.
  unfold R.v5415, N.v5415.
  rewrite ?node_5371.
  rewrite ?node_5374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5416 (s : N.State) (i : N.Inputs) :
  R.v5416 (state s) (inputs i) = Zmod.unsigned (N.v5416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5416 s i)) at 1.
  unfold R.v5416, N.v5416.
  rewrite ?node_5414.
  rewrite ?node_5415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5417 (s : N.State) (i : N.Inputs) :
  R.v5417 (state s) (inputs i) = Zmod.unsigned (N.v5417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5417 s i)) at 1.
  unfold R.v5417, N.v5417.
  rewrite ?node_5375.
  rewrite ?node_5376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5418 (s : N.State) (i : N.Inputs) :
  R.v5418 (state s) (inputs i) = Zmod.unsigned (N.v5418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5418 s i)) at 1.
  unfold R.v5418, N.v5418.
  rewrite ?node_5416.
  rewrite ?node_5417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5419 (s : N.State) (i : N.Inputs) :
  R.v5419 (state s) (inputs i) = Zmod.unsigned (N.v5419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5419 s i)) at 1.
  unfold R.v5419, N.v5419.
  rewrite ?node_5418.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2301_nr_5F2332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2301_nr_5F2332 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5420 (s : N.State) (i : N.Inputs) :
  R.v5420 (state s) (inputs i) = Zmod.unsigned (N.v5420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5420 s i)) at 1.
  unfold R.v5420, N.v5420.
  rewrite ?node_5377.
  rewrite ?node_5378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5421 (s : N.State) (i : N.Inputs) :
  R.v5421 (state s) (inputs i) = Zmod.unsigned (N.v5421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5421 s i)) at 1.
  unfold R.v5421, N.v5421.
  rewrite ?node_5420.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2302_nr_5F2333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2302_nr_5F2333 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5422 (s : N.State) (i : N.Inputs) :
  R.v5422 (state s) (inputs i) = Zmod.unsigned (N.v5422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5422 s i)) at 1.
  unfold R.v5422, N.v5422.
  rewrite !state_r79_nr_5F79.
  rewrite !state_r80_nr_5F80.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r79_nr_5F79 s)).
  rewrite ?(bits.mod_to_Z (N.r80_nr_5F80 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5423 (s : N.State) (i : N.Inputs) :
  R.v5423 (state s) (inputs i) = Zmod.unsigned (N.v5423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5423 s i)) at 1.
  unfold R.v5423, N.v5423.
  rewrite ?node_5422.
  rewrite !state_r81_nr_5F81.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r81_nr_5F81 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5424 (s : N.State) (i : N.Inputs) :
  R.v5424 (state s) (inputs i) = Zmod.unsigned (N.v5424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5424 s i)) at 1.
  unfold R.v5424, N.v5424.
  rewrite ?node_5423.
  rewrite !state_r82_nr_5F82.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r82_nr_5F82 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5425 (s : N.State) (i : N.Inputs) :
  R.v5425 (state s) (inputs i) = Zmod.unsigned (N.v5425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5425 s i)) at 1.
  unfold R.v5425, N.v5425.
  rewrite !state_r70_nr_5F70.
  rewrite !state_r71_nr_5F71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r70_nr_5F70 s)).
  rewrite ?(bits.mod_to_Z (N.r71_nr_5F71 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5426 (s : N.State) (i : N.Inputs) :
  R.v5426 (state s) (inputs i) = Zmod.unsigned (N.v5426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5426 s i)) at 1.
  unfold R.v5426, N.v5426.
  rewrite ?node_5383.
  rewrite !state_r72_nr_5F72.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r72_nr_5F72 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5427 (s : N.State) (i : N.Inputs) :
  R.v5427 (state s) (inputs i) = Zmod.unsigned (N.v5427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5427 s i)) at 1.
  unfold R.v5427, N.v5427.
  rewrite ?node_5425.
  rewrite ?node_5426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5428 (s : N.State) (i : N.Inputs) :
  R.v5428 (state s) (inputs i) = Zmod.unsigned (N.v5428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5428 s i)) at 1.
  unfold R.v5428, N.v5428.
  rewrite ?node_5424.
  rewrite ?node_5427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5429 (s : N.State) (i : N.Inputs) :
  R.v5429 (state s) (inputs i) = Zmod.unsigned (N.v5429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5429 s i)) at 1.
  unfold R.v5429, N.v5429.
  rewrite !state_r83_nr_5F83.
  rewrite !state_r84_nr_5F84.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r83_nr_5F83 s)).
  rewrite ?(bits.mod_to_Z (N.r84_nr_5F84 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5430 (s : N.State) (i : N.Inputs) :
  R.v5430 (state s) (inputs i) = Zmod.unsigned (N.v5430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5430 s i)) at 1.
  unfold R.v5430, N.v5430.
  rewrite ?node_5429.
  rewrite !state_r85_nr_5F85.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r85_nr_5F85 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5431 (s : N.State) (i : N.Inputs) :
  R.v5431 (state s) (inputs i) = Zmod.unsigned (N.v5431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5431 s i)) at 1.
  unfold R.v5431, N.v5431.
  rewrite ?node_5430.
  rewrite !state_r86_nr_5F86.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r86_nr_5F86 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5432 (s : N.State) (i : N.Inputs) :
  R.v5432 (state s) (inputs i) = Zmod.unsigned (N.v5432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5432 s i)) at 1.
  unfold R.v5432, N.v5432.
  rewrite !state_r74_nr_5F74.
  rewrite !state_r75_nr_5F75.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r74_nr_5F74 s)).
  rewrite ?(bits.mod_to_Z (N.r75_nr_5F75 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5433 (s : N.State) (i : N.Inputs) :
  R.v5433 (state s) (inputs i) = Zmod.unsigned (N.v5433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5433 s i)) at 1.
  unfold R.v5433, N.v5433.
  rewrite ?node_5390.
  rewrite !state_r76_nr_5F76.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r76_nr_5F76 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5434 (s : N.State) (i : N.Inputs) :
  R.v5434 (state s) (inputs i) = Zmod.unsigned (N.v5434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5434 s i)) at 1.
  unfold R.v5434, N.v5434.
  rewrite ?node_5432.
  rewrite ?node_5433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5435 (s : N.State) (i : N.Inputs) :
  R.v5435 (state s) (inputs i) = Zmod.unsigned (N.v5435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5435 s i)) at 1.
  unfold R.v5435, N.v5435.
  rewrite ?node_5431.
  rewrite ?node_5434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5436 (s : N.State) (i : N.Inputs) :
  R.v5436 (state s) (inputs i) = Zmod.unsigned (N.v5436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5436 s i)) at 1.
  unfold R.v5436, N.v5436.
  rewrite ?node_5428.
  rewrite ?node_5435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5437 (s : N.State) (i : N.Inputs) :
  R.v5437 (state s) (inputs i) = Zmod.unsigned (N.v5437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5437 s i)) at 1.
  unfold R.v5437, N.v5437.
  rewrite ?node_5436.
  rewrite !state_r87_nr_5F87.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r87_nr_5F87 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5438 (s : N.State) (i : N.Inputs) :
  R.v5438 (state s) (inputs i) = Zmod.unsigned (N.v5438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5438 s i)) at 1.
  unfold R.v5438, N.v5438.
  rewrite ?node_5384.
  rewrite !state_r73_nr_5F73.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r73_nr_5F73 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5439 (s : N.State) (i : N.Inputs) :
  R.v5439 (state s) (inputs i) = Zmod.unsigned (N.v5439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5439 s i)) at 1.
  unfold R.v5439, N.v5439.
  rewrite ?node_5385.
  rewrite ?node_5388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5440 (s : N.State) (i : N.Inputs) :
  R.v5440 (state s) (inputs i) = Zmod.unsigned (N.v5440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5440 s i)) at 1.
  unfold R.v5440, N.v5440.
  rewrite ?node_5438.
  rewrite ?node_5439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5441 (s : N.State) (i : N.Inputs) :
  R.v5441 (state s) (inputs i) = Zmod.unsigned (N.v5441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5441 s i)) at 1.
  unfold R.v5441, N.v5441.
  rewrite ?node_5437.
  rewrite ?node_5440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5442 (s : N.State) (i : N.Inputs) :
  R.v5442 (state s) (inputs i) = Zmod.unsigned (N.v5442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5442 s i)) at 1.
  unfold R.v5442, N.v5442.
  rewrite ?node_5389.
  rewrite ?node_5396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5443 (s : N.State) (i : N.Inputs) :
  R.v5443 (state s) (inputs i) = Zmod.unsigned (N.v5443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5443 s i)) at 1.
  unfold R.v5443, N.v5443.
  rewrite ?node_5397.
  rewrite !state_r78_nr_5F78.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r78_nr_5F78 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5444 (s : N.State) (i : N.Inputs) :
  R.v5444 (state s) (inputs i) = Zmod.unsigned (N.v5444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5444 s i)) at 1.
  unfold R.v5444, N.v5444.
  rewrite ?node_5442.
  rewrite ?node_5443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5445 (s : N.State) (i : N.Inputs) :
  R.v5445 (state s) (inputs i) = Zmod.unsigned (N.v5445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5445 s i)) at 1.
  unfold R.v5445, N.v5445.
  rewrite ?node_5441.
  rewrite ?node_5444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5446 (s : N.State) (i : N.Inputs) :
  R.v5446 (state s) (inputs i) = Zmod.unsigned (N.v5446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5446 s i)) at 1.
  unfold R.v5446, N.v5446.
  rewrite ?node_5391.
  rewrite !state_r77_nr_5F77.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r77_nr_5F77 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5447 (s : N.State) (i : N.Inputs) :
  R.v5447 (state s) (inputs i) = Zmod.unsigned (N.v5447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5447 s i)) at 1.
  unfold R.v5447, N.v5447.
  rewrite ?node_5392.
  rewrite ?node_5395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5448 (s : N.State) (i : N.Inputs) :
  R.v5448 (state s) (inputs i) = Zmod.unsigned (N.v5448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5448 s i)) at 1.
  unfold R.v5448, N.v5448.
  rewrite ?node_5446.
  rewrite ?node_5447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5449 (s : N.State) (i : N.Inputs) :
  R.v5449 (state s) (inputs i) = Zmod.unsigned (N.v5449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5449 s i)) at 1.
  unfold R.v5449, N.v5449.
  rewrite ?node_5445.
  rewrite ?node_5448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5450 (s : N.State) (i : N.Inputs) :
  R.v5450 (state s) (inputs i) = Zmod.unsigned (N.v5450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5450 s i)) at 1.
  unfold R.v5450, N.v5450.
  rewrite ?node_5398.
  rewrite ?node_5401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5451 (s : N.State) (i : N.Inputs) :
  R.v5451 (state s) (inputs i) = Zmod.unsigned (N.v5451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5451 s i)) at 1.
  unfold R.v5451, N.v5451.
  rewrite ?node_5402.
  rewrite ?node_5405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5452 (s : N.State) (i : N.Inputs) :
  R.v5452 (state s) (inputs i) = Zmod.unsigned (N.v5452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5452 s i)) at 1.
  unfold R.v5452, N.v5452.
  rewrite ?node_5450.
  rewrite ?node_5451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5453 (s : N.State) (i : N.Inputs) :
  R.v5453 (state s) (inputs i) = Zmod.unsigned (N.v5453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5453 s i)) at 1.
  unfold R.v5453, N.v5453.
  rewrite ?node_5449.
  rewrite ?node_5452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5454 (s : N.State) (i : N.Inputs) :
  R.v5454 (state s) (inputs i) = Zmod.unsigned (N.v5454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5454 s i)) at 1.
  unfold R.v5454, N.v5454.
  rewrite ?node_5406.
  rewrite ?node_5409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5455 (s : N.State) (i : N.Inputs) :
  R.v5455 (state s) (inputs i) = Zmod.unsigned (N.v5455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5455 s i)) at 1.
  unfold R.v5455, N.v5455.
  rewrite ?node_5410.
  rewrite ?node_5413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5456 (s : N.State) (i : N.Inputs) :
  R.v5456 (state s) (inputs i) = Zmod.unsigned (N.v5456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5456 s i)) at 1.
  unfold R.v5456, N.v5456.
  rewrite ?node_5454.
  rewrite ?node_5455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5457 (s : N.State) (i : N.Inputs) :
  R.v5457 (state s) (inputs i) = Zmod.unsigned (N.v5457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5457 s i)) at 1.
  unfold R.v5457, N.v5457.
  rewrite ?node_5453.
  rewrite ?node_5456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5458 (s : N.State) (i : N.Inputs) :
  R.v5458 (state s) (inputs i) = Zmod.unsigned (N.v5458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5458 s i)) at 1.
  unfold R.v5458, N.v5458.
  rewrite ?node_5414.
  rewrite ?node_5415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5459 (s : N.State) (i : N.Inputs) :
  R.v5459 (state s) (inputs i) = Zmod.unsigned (N.v5459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5459 s i)) at 1.
  unfold R.v5459, N.v5459.
  rewrite ?node_5457.
  rewrite ?node_5458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5460 (s : N.State) (i : N.Inputs) :
  R.v5460 (state s) (inputs i) = Zmod.unsigned (N.v5460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5460 s i)) at 1.
  unfold R.v5460, N.v5460.
  rewrite ?node_5459.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2303_nr_5F2334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2303_nr_5F2334 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5461 (s : N.State) (i : N.Inputs) :
  R.v5461 (state s) (inputs i) = Zmod.unsigned (N.v5461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5461 s i)) at 1.
  unfold R.v5461, N.v5461.
  rewrite ?node_5416.
  rewrite ?node_5417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5462 (s : N.State) (i : N.Inputs) :
  R.v5462 (state s) (inputs i) = Zmod.unsigned (N.v5462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5462 s i)) at 1.
  unfold R.v5462, N.v5462.
  rewrite ?node_5461.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2304_nr_5F2335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2304_nr_5F2335 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5463 (s : N.State) (i : N.Inputs) :
  R.v5463 (state s) (inputs i) = Zmod.unsigned (N.v5463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5463 s i)) at 1.
  unfold R.v5463, N.v5463.
  rewrite !state_r88_nr_5F88.
  rewrite !state_r89_nr_5F89.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r88_nr_5F88 s)).
  rewrite ?(bits.mod_to_Z (N.r89_nr_5F89 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5464 (s : N.State) (i : N.Inputs) :
  R.v5464 (state s) (inputs i) = Zmod.unsigned (N.v5464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5464 s i)) at 1.
  unfold R.v5464, N.v5464.
  rewrite ?node_5463.
  rewrite !state_r90_nr_5F90.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r90_nr_5F90 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5465 (s : N.State) (i : N.Inputs) :
  R.v5465 (state s) (inputs i) = Zmod.unsigned (N.v5465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5465 s i)) at 1.
  unfold R.v5465, N.v5465.
  rewrite ?node_5464.
  rewrite !state_r91_nr_5F91.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r91_nr_5F91 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5466 (s : N.State) (i : N.Inputs) :
  R.v5466 (state s) (inputs i) = Zmod.unsigned (N.v5466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5466 s i)) at 1.
  unfold R.v5466, N.v5466.
  rewrite !state_r79_nr_5F79.
  rewrite !state_r80_nr_5F80.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r79_nr_5F79 s)).
  rewrite ?(bits.mod_to_Z (N.r80_nr_5F80 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5467 (s : N.State) (i : N.Inputs) :
  R.v5467 (state s) (inputs i) = Zmod.unsigned (N.v5467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5467 s i)) at 1.
  unfold R.v5467, N.v5467.
  rewrite ?node_5422.
  rewrite !state_r81_nr_5F81.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r81_nr_5F81 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5468 (s : N.State) (i : N.Inputs) :
  R.v5468 (state s) (inputs i) = Zmod.unsigned (N.v5468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5468 s i)) at 1.
  unfold R.v5468, N.v5468.
  rewrite ?node_5466.
  rewrite ?node_5467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5469 (s : N.State) (i : N.Inputs) :
  R.v5469 (state s) (inputs i) = Zmod.unsigned (N.v5469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5469 s i)) at 1.
  unfold R.v5469, N.v5469.
  rewrite ?node_5465.
  rewrite ?node_5468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5470 (s : N.State) (i : N.Inputs) :
  R.v5470 (state s) (inputs i) = Zmod.unsigned (N.v5470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5470 s i)) at 1.
  unfold R.v5470, N.v5470.
  rewrite !state_r92_nr_5F92.
  rewrite !state_r93_nr_5F93.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r92_nr_5F92 s)).
  rewrite ?(bits.mod_to_Z (N.r93_nr_5F93 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5471 (s : N.State) (i : N.Inputs) :
  R.v5471 (state s) (inputs i) = Zmod.unsigned (N.v5471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5471 s i)) at 1.
  unfold R.v5471, N.v5471.
  rewrite ?node_5470.
  rewrite !state_r94_nr_5F94.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r94_nr_5F94 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5472 (s : N.State) (i : N.Inputs) :
  R.v5472 (state s) (inputs i) = Zmod.unsigned (N.v5472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5472 s i)) at 1.
  unfold R.v5472, N.v5472.
  rewrite ?node_5471.
  rewrite !state_r95_nr_5F95.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r95_nr_5F95 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5473 (s : N.State) (i : N.Inputs) :
  R.v5473 (state s) (inputs i) = Zmod.unsigned (N.v5473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5473 s i)) at 1.
  unfold R.v5473, N.v5473.
  rewrite !state_r83_nr_5F83.
  rewrite !state_r84_nr_5F84.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r83_nr_5F83 s)).
  rewrite ?(bits.mod_to_Z (N.r84_nr_5F84 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5474 (s : N.State) (i : N.Inputs) :
  R.v5474 (state s) (inputs i) = Zmod.unsigned (N.v5474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5474 s i)) at 1.
  unfold R.v5474, N.v5474.
  rewrite ?node_5429.
  rewrite !state_r85_nr_5F85.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r85_nr_5F85 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5475 (s : N.State) (i : N.Inputs) :
  R.v5475 (state s) (inputs i) = Zmod.unsigned (N.v5475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5475 s i)) at 1.
  unfold R.v5475, N.v5475.
  rewrite ?node_5473.
  rewrite ?node_5474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5476 (s : N.State) (i : N.Inputs) :
  R.v5476 (state s) (inputs i) = Zmod.unsigned (N.v5476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5476 s i)) at 1.
  unfold R.v5476, N.v5476.
  rewrite ?node_5472.
  rewrite ?node_5475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5477 (s : N.State) (i : N.Inputs) :
  R.v5477 (state s) (inputs i) = Zmod.unsigned (N.v5477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5477 s i)) at 1.
  unfold R.v5477, N.v5477.
  rewrite ?node_5469.
  rewrite ?node_5476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5478 (s : N.State) (i : N.Inputs) :
  R.v5478 (state s) (inputs i) = Zmod.unsigned (N.v5478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5478 s i)) at 1.
  unfold R.v5478, N.v5478.
  rewrite !state_r96_nr_5F96.
  rewrite !state_r97_nr_5F97.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r96_nr_5F96 s)).
  rewrite ?(bits.mod_to_Z (N.r97_nr_5F97 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5479 (s : N.State) (i : N.Inputs) :
  R.v5479 (state s) (inputs i) = Zmod.unsigned (N.v5479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5479 s i)) at 1.
  unfold R.v5479, N.v5479.
  rewrite ?node_5477.
  rewrite ?node_5478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5480 (s : N.State) (i : N.Inputs) :
  R.v5480 (state s) (inputs i) = Zmod.unsigned (N.v5480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5480 s i)) at 1.
  unfold R.v5480, N.v5480.
  rewrite ?node_5423.
  rewrite !state_r82_nr_5F82.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r82_nr_5F82 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5481 (s : N.State) (i : N.Inputs) :
  R.v5481 (state s) (inputs i) = Zmod.unsigned (N.v5481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5481 s i)) at 1.
  unfold R.v5481, N.v5481.
  rewrite ?node_5424.
  rewrite ?node_5427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5482 (s : N.State) (i : N.Inputs) :
  R.v5482 (state s) (inputs i) = Zmod.unsigned (N.v5482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5482 s i)) at 1.
  unfold R.v5482, N.v5482.
  rewrite ?node_5480.
  rewrite ?node_5481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5483 (s : N.State) (i : N.Inputs) :
  R.v5483 (state s) (inputs i) = Zmod.unsigned (N.v5483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5483 s i)) at 1.
  unfold R.v5483, N.v5483.
  rewrite ?node_5479.
  rewrite ?node_5482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5484 (s : N.State) (i : N.Inputs) :
  R.v5484 (state s) (inputs i) = Zmod.unsigned (N.v5484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5484 s i)) at 1.
  unfold R.v5484, N.v5484.
  rewrite ?node_5428.
  rewrite ?node_5435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5485 (s : N.State) (i : N.Inputs) :
  R.v5485 (state s) (inputs i) = Zmod.unsigned (N.v5485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5485 s i)) at 1.
  unfold R.v5485, N.v5485.
  rewrite ?node_5436.
  rewrite !state_r87_nr_5F87.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r87_nr_5F87 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5486 (s : N.State) (i : N.Inputs) :
  R.v5486 (state s) (inputs i) = Zmod.unsigned (N.v5486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5486 s i)) at 1.
  unfold R.v5486, N.v5486.
  rewrite ?node_5484.
  rewrite ?node_5485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5487 (s : N.State) (i : N.Inputs) :
  R.v5487 (state s) (inputs i) = Zmod.unsigned (N.v5487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5487 s i)) at 1.
  unfold R.v5487, N.v5487.
  rewrite ?node_5483.
  rewrite ?node_5486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5488 (s : N.State) (i : N.Inputs) :
  R.v5488 (state s) (inputs i) = Zmod.unsigned (N.v5488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5488 s i)) at 1.
  unfold R.v5488, N.v5488.
  rewrite ?node_5430.
  rewrite !state_r86_nr_5F86.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r86_nr_5F86 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5489 (s : N.State) (i : N.Inputs) :
  R.v5489 (state s) (inputs i) = Zmod.unsigned (N.v5489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5489 s i)) at 1.
  unfold R.v5489, N.v5489.
  rewrite ?node_5431.
  rewrite ?node_5434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5490 (s : N.State) (i : N.Inputs) :
  R.v5490 (state s) (inputs i) = Zmod.unsigned (N.v5490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5490 s i)) at 1.
  unfold R.v5490, N.v5490.
  rewrite ?node_5488.
  rewrite ?node_5489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5491 (s : N.State) (i : N.Inputs) :
  R.v5491 (state s) (inputs i) = Zmod.unsigned (N.v5491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5491 s i)) at 1.
  unfold R.v5491, N.v5491.
  rewrite ?node_5487.
  rewrite ?node_5490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5492 (s : N.State) (i : N.Inputs) :
  R.v5492 (state s) (inputs i) = Zmod.unsigned (N.v5492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5492 s i)) at 1.
  unfold R.v5492, N.v5492.
  rewrite ?node_5437.
  rewrite ?node_5440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5493 (s : N.State) (i : N.Inputs) :
  R.v5493 (state s) (inputs i) = Zmod.unsigned (N.v5493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5493 s i)) at 1.
  unfold R.v5493, N.v5493.
  rewrite ?node_5441.
  rewrite ?node_5444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5494 (s : N.State) (i : N.Inputs) :
  R.v5494 (state s) (inputs i) = Zmod.unsigned (N.v5494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5494 s i)) at 1.
  unfold R.v5494, N.v5494.
  rewrite ?node_5492.
  rewrite ?node_5493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5495 (s : N.State) (i : N.Inputs) :
  R.v5495 (state s) (inputs i) = Zmod.unsigned (N.v5495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5495 s i)) at 1.
  unfold R.v5495, N.v5495.
  rewrite ?node_5491.
  rewrite ?node_5494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5496 (s : N.State) (i : N.Inputs) :
  R.v5496 (state s) (inputs i) = Zmod.unsigned (N.v5496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5496 s i)) at 1.
  unfold R.v5496, N.v5496.
  rewrite ?node_5445.
  rewrite ?node_5448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5497 (s : N.State) (i : N.Inputs) :
  R.v5497 (state s) (inputs i) = Zmod.unsigned (N.v5497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5497 s i)) at 1.
  unfold R.v5497, N.v5497.
  rewrite ?node_5449.
  rewrite ?node_5452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5498 (s : N.State) (i : N.Inputs) :
  R.v5498 (state s) (inputs i) = Zmod.unsigned (N.v5498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5498 s i)) at 1.
  unfold R.v5498, N.v5498.
  rewrite ?node_5496.
  rewrite ?node_5497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5499 (s : N.State) (i : N.Inputs) :
  R.v5499 (state s) (inputs i) = Zmod.unsigned (N.v5499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5499 s i)) at 1.
  unfold R.v5499, N.v5499.
  rewrite ?node_5495.
  rewrite ?node_5498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5500 (s : N.State) (i : N.Inputs) :
  R.v5500 (state s) (inputs i) = Zmod.unsigned (N.v5500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5500 s i)) at 1.
  unfold R.v5500, N.v5500.
  rewrite ?node_5453.
  rewrite ?node_5456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5501 (s : N.State) (i : N.Inputs) :
  R.v5501 (state s) (inputs i) = Zmod.unsigned (N.v5501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5501 s i)) at 1.
  unfold R.v5501, N.v5501.
  rewrite ?node_5499.
  rewrite ?node_5500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5502 (s : N.State) (i : N.Inputs) :
  R.v5502 (state s) (inputs i) = Zmod.unsigned (N.v5502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5502 s i)) at 1.
  unfold R.v5502, N.v5502.
  rewrite ?node_5501.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2305_nr_5F2336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2305_nr_5F2336 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5503 (s : N.State) (i : N.Inputs) :
  R.v5503 (state s) (inputs i) = Zmod.unsigned (N.v5503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5503 s i)) at 1.
  unfold R.v5503, N.v5503.
  rewrite ?node_5457.
  rewrite ?node_5458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5504 (s : N.State) (i : N.Inputs) :
  R.v5504 (state s) (inputs i) = Zmod.unsigned (N.v5504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5504 s i)) at 1.
  unfold R.v5504, N.v5504.
  rewrite ?node_5503.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2306_nr_5F2337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2306_nr_5F2337 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5505 (s : N.State) (i : N.Inputs) :
  R.v5505 (state s) (inputs i) = Zmod.unsigned (N.v5505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5505 s i)) at 1.
  unfold R.v5505, N.v5505.
  rewrite !state_r98_nr_5F98.
  rewrite !state_r99_nr_5F99.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r98_nr_5F98 s)).
  rewrite ?(bits.mod_to_Z (N.r99_nr_5F99 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5506 (s : N.State) (i : N.Inputs) :
  R.v5506 (state s) (inputs i) = Zmod.unsigned (N.v5506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5506 s i)) at 1.
  unfold R.v5506, N.v5506.
  rewrite ?node_5505.
  rewrite !state_r100_nr_5F100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r100_nr_5F100 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5507 (s : N.State) (i : N.Inputs) :
  R.v5507 (state s) (inputs i) = Zmod.unsigned (N.v5507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5507 s i)) at 1.
  unfold R.v5507, N.v5507.
  rewrite ?node_5506.
  rewrite !state_r101_nr_5F101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r101_nr_5F101 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5508 (s : N.State) (i : N.Inputs) :
  R.v5508 (state s) (inputs i) = Zmod.unsigned (N.v5508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5508 s i)) at 1.
  unfold R.v5508, N.v5508.
  rewrite !state_r88_nr_5F88.
  rewrite !state_r89_nr_5F89.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r88_nr_5F88 s)).
  rewrite ?(bits.mod_to_Z (N.r89_nr_5F89 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5509 (s : N.State) (i : N.Inputs) :
  R.v5509 (state s) (inputs i) = Zmod.unsigned (N.v5509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5509 s i)) at 1.
  unfold R.v5509, N.v5509.
  rewrite ?node_5463.
  rewrite !state_r90_nr_5F90.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r90_nr_5F90 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5510 (s : N.State) (i : N.Inputs) :
  R.v5510 (state s) (inputs i) = Zmod.unsigned (N.v5510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5510 s i)) at 1.
  unfold R.v5510, N.v5510.
  rewrite ?node_5508.
  rewrite ?node_5509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5511 (s : N.State) (i : N.Inputs) :
  R.v5511 (state s) (inputs i) = Zmod.unsigned (N.v5511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5511 s i)) at 1.
  unfold R.v5511, N.v5511.
  rewrite ?node_5507.
  rewrite ?node_5510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5512 (s : N.State) (i : N.Inputs) :
  R.v5512 (state s) (inputs i) = Zmod.unsigned (N.v5512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5512 s i)) at 1.
  unfold R.v5512, N.v5512.
  rewrite !state_r102_nr_5F102.
  rewrite !state_r103_nr_5F103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r102_nr_5F102 s)).
  rewrite ?(bits.mod_to_Z (N.r103_nr_5F103 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5513 (s : N.State) (i : N.Inputs) :
  R.v5513 (state s) (inputs i) = Zmod.unsigned (N.v5513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5513 s i)) at 1.
  unfold R.v5513, N.v5513.
  rewrite ?node_5512.
  rewrite !state_r104_nr_5F104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r104_nr_5F104 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5514 (s : N.State) (i : N.Inputs) :
  R.v5514 (state s) (inputs i) = Zmod.unsigned (N.v5514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5514 s i)) at 1.
  unfold R.v5514, N.v5514.
  rewrite ?node_5513.
  rewrite !state_r105_nr_5F105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r105_nr_5F105 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5515 (s : N.State) (i : N.Inputs) :
  R.v5515 (state s) (inputs i) = Zmod.unsigned (N.v5515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5515 s i)) at 1.
  unfold R.v5515, N.v5515.
  rewrite !state_r92_nr_5F92.
  rewrite !state_r93_nr_5F93.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r92_nr_5F92 s)).
  rewrite ?(bits.mod_to_Z (N.r93_nr_5F93 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5516 (s : N.State) (i : N.Inputs) :
  R.v5516 (state s) (inputs i) = Zmod.unsigned (N.v5516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5516 s i)) at 1.
  unfold R.v5516, N.v5516.
  rewrite ?node_5470.
  rewrite !state_r94_nr_5F94.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r94_nr_5F94 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5517 (s : N.State) (i : N.Inputs) :
  R.v5517 (state s) (inputs i) = Zmod.unsigned (N.v5517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5517 s i)) at 1.
  unfold R.v5517, N.v5517.
  rewrite ?node_5515.
  rewrite ?node_5516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5518 (s : N.State) (i : N.Inputs) :
  R.v5518 (state s) (inputs i) = Zmod.unsigned (N.v5518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5518 s i)) at 1.
  unfold R.v5518, N.v5518.
  rewrite ?node_5514.
  rewrite ?node_5517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5519 (s : N.State) (i : N.Inputs) :
  R.v5519 (state s) (inputs i) = Zmod.unsigned (N.v5519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5519 s i)) at 1.
  unfold R.v5519, N.v5519.
  rewrite ?node_5511.
  rewrite ?node_5518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5520 (s : N.State) (i : N.Inputs) :
  R.v5520 (state s) (inputs i) = Zmod.unsigned (N.v5520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5520 s i)) at 1.
  unfold R.v5520, N.v5520.
  rewrite !state_r106_nr_5F106.
  rewrite !state_r107_nr_5F107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r106_nr_5F106 s)).
  rewrite ?(bits.mod_to_Z (N.r107_nr_5F107 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5521 (s : N.State) (i : N.Inputs) :
  R.v5521 (state s) (inputs i) = Zmod.unsigned (N.v5521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5521 s i)) at 1.
  unfold R.v5521, N.v5521.
  rewrite ?node_5519.
  rewrite ?node_5520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5522 (s : N.State) (i : N.Inputs) :
  R.v5522 (state s) (inputs i) = Zmod.unsigned (N.v5522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5522 s i)) at 1.
  unfold R.v5522, N.v5522.
  rewrite ?node_5464.
  rewrite !state_r91_nr_5F91.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r91_nr_5F91 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5523 (s : N.State) (i : N.Inputs) :
  R.v5523 (state s) (inputs i) = Zmod.unsigned (N.v5523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5523 s i)) at 1.
  unfold R.v5523, N.v5523.
  rewrite ?node_5465.
  rewrite ?node_5468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5524 (s : N.State) (i : N.Inputs) :
  R.v5524 (state s) (inputs i) = Zmod.unsigned (N.v5524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5524 s i)) at 1.
  unfold R.v5524, N.v5524.
  rewrite ?node_5522.
  rewrite ?node_5523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5525 (s : N.State) (i : N.Inputs) :
  R.v5525 (state s) (inputs i) = Zmod.unsigned (N.v5525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5525 s i)) at 1.
  unfold R.v5525, N.v5525.
  rewrite ?node_5521.
  rewrite ?node_5524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5526 (s : N.State) (i : N.Inputs) :
  R.v5526 (state s) (inputs i) = Zmod.unsigned (N.v5526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5526 s i)) at 1.
  unfold R.v5526, N.v5526.
  rewrite ?node_5469.
  rewrite ?node_5476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5527 (s : N.State) (i : N.Inputs) :
  R.v5527 (state s) (inputs i) = Zmod.unsigned (N.v5527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5527 s i)) at 1.
  unfold R.v5527, N.v5527.
  rewrite ?node_5477.
  rewrite ?node_5478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5528 (s : N.State) (i : N.Inputs) :
  R.v5528 (state s) (inputs i) = Zmod.unsigned (N.v5528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5528 s i)) at 1.
  unfold R.v5528, N.v5528.
  rewrite ?node_5526.
  rewrite ?node_5527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5529 (s : N.State) (i : N.Inputs) :
  R.v5529 (state s) (inputs i) = Zmod.unsigned (N.v5529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5529 s i)) at 1.
  unfold R.v5529, N.v5529.
  rewrite ?node_5525.
  rewrite ?node_5528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5530 (s : N.State) (i : N.Inputs) :
  R.v5530 (state s) (inputs i) = Zmod.unsigned (N.v5530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5530 s i)) at 1.
  unfold R.v5530, N.v5530.
  rewrite ?node_5471.
  rewrite !state_r95_nr_5F95.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r95_nr_5F95 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5531 (s : N.State) (i : N.Inputs) :
  R.v5531 (state s) (inputs i) = Zmod.unsigned (N.v5531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5531 s i)) at 1.
  unfold R.v5531, N.v5531.
  rewrite ?node_5472.
  rewrite ?node_5475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5532 (s : N.State) (i : N.Inputs) :
  R.v5532 (state s) (inputs i) = Zmod.unsigned (N.v5532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5532 s i)) at 1.
  unfold R.v5532, N.v5532.
  rewrite ?node_5530.
  rewrite ?node_5531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5533 (s : N.State) (i : N.Inputs) :
  R.v5533 (state s) (inputs i) = Zmod.unsigned (N.v5533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5533 s i)) at 1.
  unfold R.v5533, N.v5533.
  rewrite !state_r96_nr_5F96.
  rewrite !state_r97_nr_5F97.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r96_nr_5F96 s)).
  rewrite ?(bits.mod_to_Z (N.r97_nr_5F97 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5534 (s : N.State) (i : N.Inputs) :
  R.v5534 (state s) (inputs i) = Zmod.unsigned (N.v5534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5534 s i)) at 1.
  unfold R.v5534, N.v5534.
  rewrite ?node_5532.
  rewrite ?node_5533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5535 (s : N.State) (i : N.Inputs) :
  R.v5535 (state s) (inputs i) = Zmod.unsigned (N.v5535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5535 s i)) at 1.
  unfold R.v5535, N.v5535.
  rewrite ?node_5529.
  rewrite ?node_5534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5536 (s : N.State) (i : N.Inputs) :
  R.v5536 (state s) (inputs i) = Zmod.unsigned (N.v5536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5536 s i)) at 1.
  unfold R.v5536, N.v5536.
  rewrite ?node_5479.
  rewrite ?node_5482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5537 (s : N.State) (i : N.Inputs) :
  R.v5537 (state s) (inputs i) = Zmod.unsigned (N.v5537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5537 s i)) at 1.
  unfold R.v5537, N.v5537.
  rewrite ?node_5483.
  rewrite ?node_5486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5538 (s : N.State) (i : N.Inputs) :
  R.v5538 (state s) (inputs i) = Zmod.unsigned (N.v5538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5538 s i)) at 1.
  unfold R.v5538, N.v5538.
  rewrite ?node_5536.
  rewrite ?node_5537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5539 (s : N.State) (i : N.Inputs) :
  R.v5539 (state s) (inputs i) = Zmod.unsigned (N.v5539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5539 s i)) at 1.
  unfold R.v5539, N.v5539.
  rewrite ?node_5535.
  rewrite ?node_5538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5540 (s : N.State) (i : N.Inputs) :
  R.v5540 (state s) (inputs i) = Zmod.unsigned (N.v5540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5540 s i)) at 1.
  unfold R.v5540, N.v5540.
  rewrite ?node_5487.
  rewrite ?node_5490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5541 (s : N.State) (i : N.Inputs) :
  R.v5541 (state s) (inputs i) = Zmod.unsigned (N.v5541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5541 s i)) at 1.
  unfold R.v5541, N.v5541.
  rewrite ?node_5491.
  rewrite ?node_5494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5542 (s : N.State) (i : N.Inputs) :
  R.v5542 (state s) (inputs i) = Zmod.unsigned (N.v5542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5542 s i)) at 1.
  unfold R.v5542, N.v5542.
  rewrite ?node_5540.
  rewrite ?node_5541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5543 (s : N.State) (i : N.Inputs) :
  R.v5543 (state s) (inputs i) = Zmod.unsigned (N.v5543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5543 s i)) at 1.
  unfold R.v5543, N.v5543.
  rewrite ?node_5539.
  rewrite ?node_5542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5544 (s : N.State) (i : N.Inputs) :
  R.v5544 (state s) (inputs i) = Zmod.unsigned (N.v5544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5544 s i)) at 1.
  unfold R.v5544, N.v5544.
  rewrite ?node_5495.
  rewrite ?node_5498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5545 (s : N.State) (i : N.Inputs) :
  R.v5545 (state s) (inputs i) = Zmod.unsigned (N.v5545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5545 s i)) at 1.
  unfold R.v5545, N.v5545.
  rewrite ?node_5543.
  rewrite ?node_5544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5546 (s : N.State) (i : N.Inputs) :
  R.v5546 (state s) (inputs i) = Zmod.unsigned (N.v5546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5546 s i)) at 1.
  unfold R.v5546, N.v5546.
  rewrite ?node_5545.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2307_nr_5F2338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2307_nr_5F2338 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5547 (s : N.State) (i : N.Inputs) :
  R.v5547 (state s) (inputs i) = Zmod.unsigned (N.v5547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5547 s i)) at 1.
  unfold R.v5547, N.v5547.
  rewrite ?node_5499.
  rewrite ?node_5500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5548 (s : N.State) (i : N.Inputs) :
  R.v5548 (state s) (inputs i) = Zmod.unsigned (N.v5548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5548 s i)) at 1.
  unfold R.v5548, N.v5548.
  rewrite ?node_5547.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2308_nr_5F2339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2308_nr_5F2339 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5549 (s : N.State) (i : N.Inputs) :
  R.v5549 (state s) (inputs i) = Zmod.unsigned (N.v5549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5549 s i)) at 1.
  unfold R.v5549, N.v5549.
  rewrite !state_r108_nr_5F108.
  rewrite !state_r109_nr_5F109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r108_nr_5F108 s)).
  rewrite ?(bits.mod_to_Z (N.r109_nr_5F109 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5550 (s : N.State) (i : N.Inputs) :
  R.v5550 (state s) (inputs i) = Zmod.unsigned (N.v5550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5550 s i)) at 1.
  unfold R.v5550, N.v5550.
  rewrite ?node_5549.
  rewrite !state_r110_nr_5F110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r110_nr_5F110 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5551 (s : N.State) (i : N.Inputs) :
  R.v5551 (state s) (inputs i) = Zmod.unsigned (N.v5551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5551 s i)) at 1.
  unfold R.v5551, N.v5551.
  rewrite ?node_5550.
  rewrite !state_r111_nr_5F111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r111_nr_5F111 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5552 (s : N.State) (i : N.Inputs) :
  R.v5552 (state s) (inputs i) = Zmod.unsigned (N.v5552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5552 s i)) at 1.
  unfold R.v5552, N.v5552.
  rewrite !state_r98_nr_5F98.
  rewrite !state_r99_nr_5F99.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r98_nr_5F98 s)).
  rewrite ?(bits.mod_to_Z (N.r99_nr_5F99 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5553 (s : N.State) (i : N.Inputs) :
  R.v5553 (state s) (inputs i) = Zmod.unsigned (N.v5553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5553 s i)) at 1.
  unfold R.v5553, N.v5553.
  rewrite ?node_5505.
  rewrite !state_r100_nr_5F100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r100_nr_5F100 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5554 (s : N.State) (i : N.Inputs) :
  R.v5554 (state s) (inputs i) = Zmod.unsigned (N.v5554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5554 s i)) at 1.
  unfold R.v5554, N.v5554.
  rewrite ?node_5552.
  rewrite ?node_5553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5555 (s : N.State) (i : N.Inputs) :
  R.v5555 (state s) (inputs i) = Zmod.unsigned (N.v5555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5555 s i)) at 1.
  unfold R.v5555, N.v5555.
  rewrite ?node_5551.
  rewrite ?node_5554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5556 (s : N.State) (i : N.Inputs) :
  R.v5556 (state s) (inputs i) = Zmod.unsigned (N.v5556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5556 s i)) at 1.
  unfold R.v5556, N.v5556.
  rewrite !state_r112_nr_5F112.
  rewrite !state_r113_nr_5F113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r112_nr_5F112 s)).
  rewrite ?(bits.mod_to_Z (N.r113_nr_5F113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5557 (s : N.State) (i : N.Inputs) :
  R.v5557 (state s) (inputs i) = Zmod.unsigned (N.v5557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5557 s i)) at 1.
  unfold R.v5557, N.v5557.
  rewrite ?node_5556.
  rewrite !state_r114_nr_5F114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r114_nr_5F114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5558 (s : N.State) (i : N.Inputs) :
  R.v5558 (state s) (inputs i) = Zmod.unsigned (N.v5558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5558 s i)) at 1.
  unfold R.v5558, N.v5558.
  rewrite ?node_5557.
  rewrite !state_r115_nr_5F115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r115_nr_5F115 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5559 (s : N.State) (i : N.Inputs) :
  R.v5559 (state s) (inputs i) = Zmod.unsigned (N.v5559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5559 s i)) at 1.
  unfold R.v5559, N.v5559.
  rewrite !state_r102_nr_5F102.
  rewrite !state_r103_nr_5F103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r102_nr_5F102 s)).
  rewrite ?(bits.mod_to_Z (N.r103_nr_5F103 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5560 (s : N.State) (i : N.Inputs) :
  R.v5560 (state s) (inputs i) = Zmod.unsigned (N.v5560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5560 s i)) at 1.
  unfold R.v5560, N.v5560.
  rewrite ?node_5512.
  rewrite !state_r104_nr_5F104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r104_nr_5F104 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5561 (s : N.State) (i : N.Inputs) :
  R.v5561 (state s) (inputs i) = Zmod.unsigned (N.v5561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5561 s i)) at 1.
  unfold R.v5561, N.v5561.
  rewrite ?node_5559.
  rewrite ?node_5560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5562 (s : N.State) (i : N.Inputs) :
  R.v5562 (state s) (inputs i) = Zmod.unsigned (N.v5562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5562 s i)) at 1.
  unfold R.v5562, N.v5562.
  rewrite ?node_5558.
  rewrite ?node_5561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5563 (s : N.State) (i : N.Inputs) :
  R.v5563 (state s) (inputs i) = Zmod.unsigned (N.v5563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5563 s i)) at 1.
  unfold R.v5563, N.v5563.
  rewrite ?node_5555.
  rewrite ?node_5562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5564 (s : N.State) (i : N.Inputs) :
  R.v5564 (state s) (inputs i) = Zmod.unsigned (N.v5564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5564 s i)) at 1.
  unfold R.v5564, N.v5564.
  rewrite !state_r116_nr_5F116.
  rewrite !state_r117_nr_5F117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r116_nr_5F116 s)).
  rewrite ?(bits.mod_to_Z (N.r117_nr_5F117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5565 (s : N.State) (i : N.Inputs) :
  R.v5565 (state s) (inputs i) = Zmod.unsigned (N.v5565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5565 s i)) at 1.
  unfold R.v5565, N.v5565.
  rewrite ?node_5564.
  rewrite !state_r118_nr_5F118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r118_nr_5F118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5566 (s : N.State) (i : N.Inputs) :
  R.v5566 (state s) (inputs i) = Zmod.unsigned (N.v5566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5566 s i)) at 1.
  unfold R.v5566, N.v5566.
  rewrite ?node_5563.
  rewrite ?node_5565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5567 (s : N.State) (i : N.Inputs) :
  R.v5567 (state s) (inputs i) = Zmod.unsigned (N.v5567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5567 s i)) at 1.
  unfold R.v5567, N.v5567.
  rewrite ?node_5506.
  rewrite !state_r101_nr_5F101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r101_nr_5F101 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5568 (s : N.State) (i : N.Inputs) :
  R.v5568 (state s) (inputs i) = Zmod.unsigned (N.v5568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5568 s i)) at 1.
  unfold R.v5568, N.v5568.
  rewrite ?node_5507.
  rewrite ?node_5510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5569 (s : N.State) (i : N.Inputs) :
  R.v5569 (state s) (inputs i) = Zmod.unsigned (N.v5569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5569 s i)) at 1.
  unfold R.v5569, N.v5569.
  rewrite ?node_5567.
  rewrite ?node_5568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5570 (s : N.State) (i : N.Inputs) :
  R.v5570 (state s) (inputs i) = Zmod.unsigned (N.v5570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5570 s i)) at 1.
  unfold R.v5570, N.v5570.
  rewrite ?node_5566.
  rewrite ?node_5569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5571 (s : N.State) (i : N.Inputs) :
  R.v5571 (state s) (inputs i) = Zmod.unsigned (N.v5571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5571 s i)) at 1.
  unfold R.v5571, N.v5571.
  rewrite ?node_5511.
  rewrite ?node_5518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5572 (s : N.State) (i : N.Inputs) :
  R.v5572 (state s) (inputs i) = Zmod.unsigned (N.v5572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5572 s i)) at 1.
  unfold R.v5572, N.v5572.
  rewrite ?node_5519.
  rewrite ?node_5520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5573 (s : N.State) (i : N.Inputs) :
  R.v5573 (state s) (inputs i) = Zmod.unsigned (N.v5573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5573 s i)) at 1.
  unfold R.v5573, N.v5573.
  rewrite ?node_5571.
  rewrite ?node_5572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5574 (s : N.State) (i : N.Inputs) :
  R.v5574 (state s) (inputs i) = Zmod.unsigned (N.v5574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5574 s i)) at 1.
  unfold R.v5574, N.v5574.
  rewrite ?node_5570.
  rewrite ?node_5573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5575 (s : N.State) (i : N.Inputs) :
  R.v5575 (state s) (inputs i) = Zmod.unsigned (N.v5575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5575 s i)) at 1.
  unfold R.v5575, N.v5575.
  rewrite ?node_5513.
  rewrite !state_r105_nr_5F105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r105_nr_5F105 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5576 (s : N.State) (i : N.Inputs) :
  R.v5576 (state s) (inputs i) = Zmod.unsigned (N.v5576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5576 s i)) at 1.
  unfold R.v5576, N.v5576.
  rewrite ?node_5514.
  rewrite ?node_5517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5577 (s : N.State) (i : N.Inputs) :
  R.v5577 (state s) (inputs i) = Zmod.unsigned (N.v5577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5577 s i)) at 1.
  unfold R.v5577, N.v5577.
  rewrite ?node_5575.
  rewrite ?node_5576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5578 (s : N.State) (i : N.Inputs) :
  R.v5578 (state s) (inputs i) = Zmod.unsigned (N.v5578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5578 s i)) at 1.
  unfold R.v5578, N.v5578.
  rewrite !state_r106_nr_5F106.
  rewrite !state_r107_nr_5F107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r106_nr_5F106 s)).
  rewrite ?(bits.mod_to_Z (N.r107_nr_5F107 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5579 (s : N.State) (i : N.Inputs) :
  R.v5579 (state s) (inputs i) = Zmod.unsigned (N.v5579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5579 s i)) at 1.
  unfold R.v5579, N.v5579.
  rewrite ?node_5577.
  rewrite ?node_5578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5580 (s : N.State) (i : N.Inputs) :
  R.v5580 (state s) (inputs i) = Zmod.unsigned (N.v5580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5580 s i)) at 1.
  unfold R.v5580, N.v5580.
  rewrite ?node_5574.
  rewrite ?node_5579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5581 (s : N.State) (i : N.Inputs) :
  R.v5581 (state s) (inputs i) = Zmod.unsigned (N.v5581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5581 s i)) at 1.
  unfold R.v5581, N.v5581.
  rewrite ?node_5521.
  rewrite ?node_5524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5582 (s : N.State) (i : N.Inputs) :
  R.v5582 (state s) (inputs i) = Zmod.unsigned (N.v5582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5582 s i)) at 1.
  unfold R.v5582, N.v5582.
  rewrite ?node_5525.
  rewrite ?node_5528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5583 (s : N.State) (i : N.Inputs) :
  R.v5583 (state s) (inputs i) = Zmod.unsigned (N.v5583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5583 s i)) at 1.
  unfold R.v5583, N.v5583.
  rewrite ?node_5581.
  rewrite ?node_5582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5584 (s : N.State) (i : N.Inputs) :
  R.v5584 (state s) (inputs i) = Zmod.unsigned (N.v5584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5584 s i)) at 1.
  unfold R.v5584, N.v5584.
  rewrite ?node_5580.
  rewrite ?node_5583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5585 (s : N.State) (i : N.Inputs) :
  R.v5585 (state s) (inputs i) = Zmod.unsigned (N.v5585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5585 s i)) at 1.
  unfold R.v5585, N.v5585.
  rewrite ?node_5532.
  rewrite ?node_5533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5586 (s : N.State) (i : N.Inputs) :
  R.v5586 (state s) (inputs i) = Zmod.unsigned (N.v5586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5586 s i)) at 1.
  unfold R.v5586, N.v5586.
  rewrite ?node_5584.
  rewrite ?node_5585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5587 (s : N.State) (i : N.Inputs) :
  R.v5587 (state s) (inputs i) = Zmod.unsigned (N.v5587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5587 s i)) at 1.
  unfold R.v5587, N.v5587.
  rewrite ?node_5529.
  rewrite ?node_5534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5588 (s : N.State) (i : N.Inputs) :
  R.v5588 (state s) (inputs i) = Zmod.unsigned (N.v5588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5588 s i)) at 1.
  unfold R.v5588, N.v5588.
  rewrite ?node_5535.
  rewrite ?node_5538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5589 (s : N.State) (i : N.Inputs) :
  R.v5589 (state s) (inputs i) = Zmod.unsigned (N.v5589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5589 s i)) at 1.
  unfold R.v5589, N.v5589.
  rewrite ?node_5587.
  rewrite ?node_5588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5590 (s : N.State) (i : N.Inputs) :
  R.v5590 (state s) (inputs i) = Zmod.unsigned (N.v5590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5590 s i)) at 1.
  unfold R.v5590, N.v5590.
  rewrite ?node_5586.
  rewrite ?node_5589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5591 (s : N.State) (i : N.Inputs) :
  R.v5591 (state s) (inputs i) = Zmod.unsigned (N.v5591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5591 s i)) at 1.
  unfold R.v5591, N.v5591.
  rewrite ?node_5539.
  rewrite ?node_5542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5592 (s : N.State) (i : N.Inputs) :
  R.v5592 (state s) (inputs i) = Zmod.unsigned (N.v5592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5592 s i)) at 1.
  unfold R.v5592, N.v5592.
  rewrite ?node_5590.
  rewrite ?node_5591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5593 (s : N.State) (i : N.Inputs) :
  R.v5593 (state s) (inputs i) = Zmod.unsigned (N.v5593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5593 s i)) at 1.
  unfold R.v5593, N.v5593.
  rewrite ?node_5592.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2309_nr_5F2340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2309_nr_5F2340 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5594 (s : N.State) (i : N.Inputs) :
  R.v5594 (state s) (inputs i) = Zmod.unsigned (N.v5594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5594 s i)) at 1.
  unfold R.v5594, N.v5594.
  rewrite ?node_5543.
  rewrite ?node_5544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5595 (s : N.State) (i : N.Inputs) :
  R.v5595 (state s) (inputs i) = Zmod.unsigned (N.v5595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5595 s i)) at 1.
  unfold R.v5595, N.v5595.
  rewrite ?node_5594.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2310_nr_5F2341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2310_nr_5F2341 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5596 (s : N.State) (i : N.Inputs) :
  R.v5596 (state s) (inputs i) = Zmod.unsigned (N.v5596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5596 s i)) at 1.
  unfold R.v5596, N.v5596.
  rewrite !state_r119_nr_5F119.
  rewrite !state_r120_nr_5F120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r119_nr_5F119 s)).
  rewrite ?(bits.mod_to_Z (N.r120_nr_5F120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5597 (s : N.State) (i : N.Inputs) :
  R.v5597 (state s) (inputs i) = Zmod.unsigned (N.v5597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5597 s i)) at 1.
  unfold R.v5597, N.v5597.
  rewrite ?node_5596.
  rewrite !state_r121_nr_5F121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r121_nr_5F121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5598 (s : N.State) (i : N.Inputs) :
  R.v5598 (state s) (inputs i) = Zmod.unsigned (N.v5598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5598 s i)) at 1.
  unfold R.v5598, N.v5598.
  rewrite ?node_5597.
  rewrite !state_r122_nr_5F122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r122_nr_5F122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5599 (s : N.State) (i : N.Inputs) :
  R.v5599 (state s) (inputs i) = Zmod.unsigned (N.v5599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5599 s i)) at 1.
  unfold R.v5599, N.v5599.
  rewrite !state_r108_nr_5F108.
  rewrite !state_r109_nr_5F109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r108_nr_5F108 s)).
  rewrite ?(bits.mod_to_Z (N.r109_nr_5F109 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5600 (s : N.State) (i : N.Inputs) :
  R.v5600 (state s) (inputs i) = Zmod.unsigned (N.v5600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5600 s i)) at 1.
  unfold R.v5600, N.v5600.
  rewrite ?node_5549.
  rewrite !state_r110_nr_5F110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r110_nr_5F110 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5601 (s : N.State) (i : N.Inputs) :
  R.v5601 (state s) (inputs i) = Zmod.unsigned (N.v5601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5601 s i)) at 1.
  unfold R.v5601, N.v5601.
  rewrite ?node_5599.
  rewrite ?node_5600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5602 (s : N.State) (i : N.Inputs) :
  R.v5602 (state s) (inputs i) = Zmod.unsigned (N.v5602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5602 s i)) at 1.
  unfold R.v5602, N.v5602.
  rewrite ?node_5598.
  rewrite ?node_5601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5603 (s : N.State) (i : N.Inputs) :
  R.v5603 (state s) (inputs i) = Zmod.unsigned (N.v5603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5603 s i)) at 1.
  unfold R.v5603, N.v5603.
  rewrite !state_r123_nr_5F123.
  rewrite !state_r124_nr_5F124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r123_nr_5F123 s)).
  rewrite ?(bits.mod_to_Z (N.r124_nr_5F124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5604 (s : N.State) (i : N.Inputs) :
  R.v5604 (state s) (inputs i) = Zmod.unsigned (N.v5604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5604 s i)) at 1.
  unfold R.v5604, N.v5604.
  rewrite ?node_5603.
  rewrite !state_r125_nr_5F125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r125_nr_5F125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5605 (s : N.State) (i : N.Inputs) :
  R.v5605 (state s) (inputs i) = Zmod.unsigned (N.v5605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5605 s i)) at 1.
  unfold R.v5605, N.v5605.
  rewrite ?node_5604.
  rewrite !state_r126_nr_5F126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r126_nr_5F126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5606 (s : N.State) (i : N.Inputs) :
  R.v5606 (state s) (inputs i) = Zmod.unsigned (N.v5606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5606 s i)) at 1.
  unfold R.v5606, N.v5606.
  rewrite !state_r112_nr_5F112.
  rewrite !state_r113_nr_5F113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r112_nr_5F112 s)).
  rewrite ?(bits.mod_to_Z (N.r113_nr_5F113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5607 (s : N.State) (i : N.Inputs) :
  R.v5607 (state s) (inputs i) = Zmod.unsigned (N.v5607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5607 s i)) at 1.
  unfold R.v5607, N.v5607.
  rewrite ?node_5556.
  rewrite !state_r114_nr_5F114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r114_nr_5F114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5608 (s : N.State) (i : N.Inputs) :
  R.v5608 (state s) (inputs i) = Zmod.unsigned (N.v5608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5608 s i)) at 1.
  unfold R.v5608, N.v5608.
  rewrite ?node_5606.
  rewrite ?node_5607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5609 (s : N.State) (i : N.Inputs) :
  R.v5609 (state s) (inputs i) = Zmod.unsigned (N.v5609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5609 s i)) at 1.
  unfold R.v5609, N.v5609.
  rewrite ?node_5605.
  rewrite ?node_5608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5610 (s : N.State) (i : N.Inputs) :
  R.v5610 (state s) (inputs i) = Zmod.unsigned (N.v5610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5610 s i)) at 1.
  unfold R.v5610, N.v5610.
  rewrite ?node_5602.
  rewrite ?node_5609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5611 (s : N.State) (i : N.Inputs) :
  R.v5611 (state s) (inputs i) = Zmod.unsigned (N.v5611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5611 s i)) at 1.
  unfold R.v5611, N.v5611.
  rewrite !state_r127_nr_5F127.
  rewrite !state_r128_nr_5F128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r127_nr_5F127 s)).
  rewrite ?(bits.mod_to_Z (N.r128_nr_5F128 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5612 (s : N.State) (i : N.Inputs) :
  R.v5612 (state s) (inputs i) = Zmod.unsigned (N.v5612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5612 s i)) at 1.
  unfold R.v5612, N.v5612.
  rewrite ?node_5611.
  rewrite !state_r129_nr_5F129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r129_nr_5F129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5613 (s : N.State) (i : N.Inputs) :
  R.v5613 (state s) (inputs i) = Zmod.unsigned (N.v5613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5613 s i)) at 1.
  unfold R.v5613, N.v5613.
  rewrite ?node_5610.
  rewrite ?node_5612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5614 (s : N.State) (i : N.Inputs) :
  R.v5614 (state s) (inputs i) = Zmod.unsigned (N.v5614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5614 s i)) at 1.
  unfold R.v5614, N.v5614.
  rewrite ?node_5550.
  rewrite !state_r111_nr_5F111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r111_nr_5F111 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5615 (s : N.State) (i : N.Inputs) :
  R.v5615 (state s) (inputs i) = Zmod.unsigned (N.v5615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5615 s i)) at 1.
  unfold R.v5615, N.v5615.
  rewrite ?node_5551.
  rewrite ?node_5554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5616 (s : N.State) (i : N.Inputs) :
  R.v5616 (state s) (inputs i) = Zmod.unsigned (N.v5616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5616 s i)) at 1.
  unfold R.v5616, N.v5616.
  rewrite ?node_5614.
  rewrite ?node_5615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5617 (s : N.State) (i : N.Inputs) :
  R.v5617 (state s) (inputs i) = Zmod.unsigned (N.v5617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5617 s i)) at 1.
  unfold R.v5617, N.v5617.
  rewrite ?node_5613.
  rewrite ?node_5616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5618 (s : N.State) (i : N.Inputs) :
  R.v5618 (state s) (inputs i) = Zmod.unsigned (N.v5618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5618 s i)) at 1.
  unfold R.v5618, N.v5618.
  rewrite ?node_5555.
  rewrite ?node_5562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5619 (s : N.State) (i : N.Inputs) :
  R.v5619 (state s) (inputs i) = Zmod.unsigned (N.v5619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5619 s i)) at 1.
  unfold R.v5619, N.v5619.
  rewrite ?node_5563.
  rewrite ?node_5565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5620 (s : N.State) (i : N.Inputs) :
  R.v5620 (state s) (inputs i) = Zmod.unsigned (N.v5620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5620 s i)) at 1.
  unfold R.v5620, N.v5620.
  rewrite ?node_5618.
  rewrite ?node_5619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5621 (s : N.State) (i : N.Inputs) :
  R.v5621 (state s) (inputs i) = Zmod.unsigned (N.v5621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5621 s i)) at 1.
  unfold R.v5621, N.v5621.
  rewrite ?node_5617.
  rewrite ?node_5620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5622 (s : N.State) (i : N.Inputs) :
  R.v5622 (state s) (inputs i) = Zmod.unsigned (N.v5622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5622 s i)) at 1.
  unfold R.v5622, N.v5622.
  rewrite ?node_5557.
  rewrite !state_r115_nr_5F115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r115_nr_5F115 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5623 (s : N.State) (i : N.Inputs) :
  R.v5623 (state s) (inputs i) = Zmod.unsigned (N.v5623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5623 s i)) at 1.
  unfold R.v5623, N.v5623.
  rewrite ?node_5558.
  rewrite ?node_5561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5624 (s : N.State) (i : N.Inputs) :
  R.v5624 (state s) (inputs i) = Zmod.unsigned (N.v5624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5624 s i)) at 1.
  unfold R.v5624, N.v5624.
  rewrite ?node_5622.
  rewrite ?node_5623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5625 (s : N.State) (i : N.Inputs) :
  R.v5625 (state s) (inputs i) = Zmod.unsigned (N.v5625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5625 s i)) at 1.
  unfold R.v5625, N.v5625.
  rewrite !state_r116_nr_5F116.
  rewrite !state_r117_nr_5F117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r116_nr_5F116 s)).
  rewrite ?(bits.mod_to_Z (N.r117_nr_5F117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5626 (s : N.State) (i : N.Inputs) :
  R.v5626 (state s) (inputs i) = Zmod.unsigned (N.v5626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5626 s i)) at 1.
  unfold R.v5626, N.v5626.
  rewrite ?node_5564.
  rewrite !state_r118_nr_5F118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r118_nr_5F118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5627 (s : N.State) (i : N.Inputs) :
  R.v5627 (state s) (inputs i) = Zmod.unsigned (N.v5627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5627 s i)) at 1.
  unfold R.v5627, N.v5627.
  rewrite ?node_5625.
  rewrite ?node_5626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5628 (s : N.State) (i : N.Inputs) :
  R.v5628 (state s) (inputs i) = Zmod.unsigned (N.v5628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5628 s i)) at 1.
  unfold R.v5628, N.v5628.
  rewrite ?node_5624.
  rewrite ?node_5627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5629 (s : N.State) (i : N.Inputs) :
  R.v5629 (state s) (inputs i) = Zmod.unsigned (N.v5629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5629 s i)) at 1.
  unfold R.v5629, N.v5629.
  rewrite ?node_5621.
  rewrite ?node_5628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5630 (s : N.State) (i : N.Inputs) :
  R.v5630 (state s) (inputs i) = Zmod.unsigned (N.v5630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5630 s i)) at 1.
  unfold R.v5630, N.v5630.
  rewrite ?node_5566.
  rewrite ?node_5569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5631 (s : N.State) (i : N.Inputs) :
  R.v5631 (state s) (inputs i) = Zmod.unsigned (N.v5631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5631 s i)) at 1.
  unfold R.v5631, N.v5631.
  rewrite ?node_5570.
  rewrite ?node_5573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5632 (s : N.State) (i : N.Inputs) :
  R.v5632 (state s) (inputs i) = Zmod.unsigned (N.v5632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5632 s i)) at 1.
  unfold R.v5632, N.v5632.
  rewrite ?node_5630.
  rewrite ?node_5631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5633 (s : N.State) (i : N.Inputs) :
  R.v5633 (state s) (inputs i) = Zmod.unsigned (N.v5633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5633 s i)) at 1.
  unfold R.v5633, N.v5633.
  rewrite ?node_5629.
  rewrite ?node_5632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5634 (s : N.State) (i : N.Inputs) :
  R.v5634 (state s) (inputs i) = Zmod.unsigned (N.v5634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5634 s i)) at 1.
  unfold R.v5634, N.v5634.
  rewrite ?node_5577.
  rewrite ?node_5578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5635 (s : N.State) (i : N.Inputs) :
  R.v5635 (state s) (inputs i) = Zmod.unsigned (N.v5635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5635 s i)) at 1.
  unfold R.v5635, N.v5635.
  rewrite ?node_5633.
  rewrite ?node_5634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5636 (s : N.State) (i : N.Inputs) :
  R.v5636 (state s) (inputs i) = Zmod.unsigned (N.v5636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5636 s i)) at 1.
  unfold R.v5636, N.v5636.
  rewrite ?node_5574.
  rewrite ?node_5579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5637 (s : N.State) (i : N.Inputs) :
  R.v5637 (state s) (inputs i) = Zmod.unsigned (N.v5637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5637 s i)) at 1.
  unfold R.v5637, N.v5637.
  rewrite ?node_5580.
  rewrite ?node_5583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5638 (s : N.State) (i : N.Inputs) :
  R.v5638 (state s) (inputs i) = Zmod.unsigned (N.v5638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5638 s i)) at 1.
  unfold R.v5638, N.v5638.
  rewrite ?node_5636.
  rewrite ?node_5637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5639 (s : N.State) (i : N.Inputs) :
  R.v5639 (state s) (inputs i) = Zmod.unsigned (N.v5639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5639 s i)) at 1.
  unfold R.v5639, N.v5639.
  rewrite ?node_5635.
  rewrite ?node_5638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5640 (s : N.State) (i : N.Inputs) :
  R.v5640 (state s) (inputs i) = Zmod.unsigned (N.v5640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5640 s i)) at 1.
  unfold R.v5640, N.v5640.
  rewrite ?node_5584.
  rewrite ?node_5585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5641 (s : N.State) (i : N.Inputs) :
  R.v5641 (state s) (inputs i) = Zmod.unsigned (N.v5641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5641 s i)) at 1.
  unfold R.v5641, N.v5641.
  rewrite ?node_5639.
  rewrite ?node_5640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5642 (s : N.State) (i : N.Inputs) :
  R.v5642 (state s) (inputs i) = Zmod.unsigned (N.v5642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5642 s i)) at 1.
  unfold R.v5642, N.v5642.
  rewrite ?node_5586.
  rewrite ?node_5589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5643 (s : N.State) (i : N.Inputs) :
  R.v5643 (state s) (inputs i) = Zmod.unsigned (N.v5643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5643 s i)) at 1.
  unfold R.v5643, N.v5643.
  rewrite ?node_5641.
  rewrite ?node_5642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5644 (s : N.State) (i : N.Inputs) :
  R.v5644 (state s) (inputs i) = Zmod.unsigned (N.v5644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5644 s i)) at 1.
  unfold R.v5644, N.v5644.
  rewrite ?node_5643.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2311_nr_5F2342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2311_nr_5F2342 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5645 (s : N.State) (i : N.Inputs) :
  R.v5645 (state s) (inputs i) = Zmod.unsigned (N.v5645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5645 s i)) at 1.
  unfold R.v5645, N.v5645.
  rewrite ?node_5590.
  rewrite ?node_5591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5646 (s : N.State) (i : N.Inputs) :
  R.v5646 (state s) (inputs i) = Zmod.unsigned (N.v5646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5646 s i)) at 1.
  unfold R.v5646, N.v5646.
  rewrite ?node_5645.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2312_nr_5F2343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2312_nr_5F2343 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5647 (s : N.State) (i : N.Inputs) :
  R.v5647 (state s) (inputs i) = Zmod.unsigned (N.v5647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5647 s i)) at 1.
  unfold R.v5647, N.v5647.
  rewrite !state_r130_nr_5F130.
  rewrite !state_r131_nr_5F131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r130_nr_5F130 s)).
  rewrite ?(bits.mod_to_Z (N.r131_nr_5F131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5648 (s : N.State) (i : N.Inputs) :
  R.v5648 (state s) (inputs i) = Zmod.unsigned (N.v5648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5648 s i)) at 1.
  unfold R.v5648, N.v5648.
  rewrite ?node_5647.
  rewrite !state_r132_nr_5F132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r132_nr_5F132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5649 (s : N.State) (i : N.Inputs) :
  R.v5649 (state s) (inputs i) = Zmod.unsigned (N.v5649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5649 s i)) at 1.
  unfold R.v5649, N.v5649.
  rewrite ?node_5648.
  rewrite !state_r133_nr_5F133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r133_nr_5F133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5650 (s : N.State) (i : N.Inputs) :
  R.v5650 (state s) (inputs i) = Zmod.unsigned (N.v5650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5650 s i)) at 1.
  unfold R.v5650, N.v5650.
  rewrite !state_r119_nr_5F119.
  rewrite !state_r120_nr_5F120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r119_nr_5F119 s)).
  rewrite ?(bits.mod_to_Z (N.r120_nr_5F120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5651 (s : N.State) (i : N.Inputs) :
  R.v5651 (state s) (inputs i) = Zmod.unsigned (N.v5651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5651 s i)) at 1.
  unfold R.v5651, N.v5651.
  rewrite ?node_5596.
  rewrite !state_r121_nr_5F121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r121_nr_5F121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5652 (s : N.State) (i : N.Inputs) :
  R.v5652 (state s) (inputs i) = Zmod.unsigned (N.v5652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5652 s i)) at 1.
  unfold R.v5652, N.v5652.
  rewrite ?node_5650.
  rewrite ?node_5651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5653 (s : N.State) (i : N.Inputs) :
  R.v5653 (state s) (inputs i) = Zmod.unsigned (N.v5653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5653 s i)) at 1.
  unfold R.v5653, N.v5653.
  rewrite ?node_5649.
  rewrite ?node_5652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5654 (s : N.State) (i : N.Inputs) :
  R.v5654 (state s) (inputs i) = Zmod.unsigned (N.v5654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5654 s i)) at 1.
  unfold R.v5654, N.v5654.
  rewrite !state_r134_nr_5F134.
  rewrite !state_r135_nr_5F135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r134_nr_5F134 s)).
  rewrite ?(bits.mod_to_Z (N.r135_nr_5F135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5655 (s : N.State) (i : N.Inputs) :
  R.v5655 (state s) (inputs i) = Zmod.unsigned (N.v5655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5655 s i)) at 1.
  unfold R.v5655, N.v5655.
  rewrite ?node_5654.
  rewrite !state_r136_nr_5F136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r136_nr_5F136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5656 (s : N.State) (i : N.Inputs) :
  R.v5656 (state s) (inputs i) = Zmod.unsigned (N.v5656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5656 s i)) at 1.
  unfold R.v5656, N.v5656.
  rewrite ?node_5655.
  rewrite !state_r137_nr_5F137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r137_nr_5F137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5657 (s : N.State) (i : N.Inputs) :
  R.v5657 (state s) (inputs i) = Zmod.unsigned (N.v5657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5657 s i)) at 1.
  unfold R.v5657, N.v5657.
  rewrite !state_r123_nr_5F123.
  rewrite !state_r124_nr_5F124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r123_nr_5F123 s)).
  rewrite ?(bits.mod_to_Z (N.r124_nr_5F124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5658 (s : N.State) (i : N.Inputs) :
  R.v5658 (state s) (inputs i) = Zmod.unsigned (N.v5658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5658 s i)) at 1.
  unfold R.v5658, N.v5658.
  rewrite ?node_5603.
  rewrite !state_r125_nr_5F125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r125_nr_5F125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5659 (s : N.State) (i : N.Inputs) :
  R.v5659 (state s) (inputs i) = Zmod.unsigned (N.v5659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5659 s i)) at 1.
  unfold R.v5659, N.v5659.
  rewrite ?node_5657.
  rewrite ?node_5658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5660 (s : N.State) (i : N.Inputs) :
  R.v5660 (state s) (inputs i) = Zmod.unsigned (N.v5660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5660 s i)) at 1.
  unfold R.v5660, N.v5660.
  rewrite ?node_5656.
  rewrite ?node_5659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5661 (s : N.State) (i : N.Inputs) :
  R.v5661 (state s) (inputs i) = Zmod.unsigned (N.v5661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5661 s i)) at 1.
  unfold R.v5661, N.v5661.
  rewrite ?node_5653.
  rewrite ?node_5660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5662 (s : N.State) (i : N.Inputs) :
  R.v5662 (state s) (inputs i) = Zmod.unsigned (N.v5662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5662 s i)) at 1.
  unfold R.v5662, N.v5662.
  rewrite !state_r138_nr_5F138.
  rewrite !state_r139_nr_5F139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r138_nr_5F138 s)).
  rewrite ?(bits.mod_to_Z (N.r139_nr_5F139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5663 (s : N.State) (i : N.Inputs) :
  R.v5663 (state s) (inputs i) = Zmod.unsigned (N.v5663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5663 s i)) at 1.
  unfold R.v5663, N.v5663.
  rewrite ?node_5662.
  rewrite !state_r140_nr_5F140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r140_nr_5F140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5664 (s : N.State) (i : N.Inputs) :
  R.v5664 (state s) (inputs i) = Zmod.unsigned (N.v5664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5664 s i)) at 1.
  unfold R.v5664, N.v5664.
  rewrite ?node_5663.
  rewrite !state_r141_nr_5F141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r141_nr_5F141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5665 (s : N.State) (i : N.Inputs) :
  R.v5665 (state s) (inputs i) = Zmod.unsigned (N.v5665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5665 s i)) at 1.
  unfold R.v5665, N.v5665.
  rewrite ?node_5661.
  rewrite ?node_5664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5666 (s : N.State) (i : N.Inputs) :
  R.v5666 (state s) (inputs i) = Zmod.unsigned (N.v5666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5666 s i)) at 1.
  unfold R.v5666, N.v5666.
  rewrite ?node_5597.
  rewrite !state_r122_nr_5F122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r122_nr_5F122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5667 (s : N.State) (i : N.Inputs) :
  R.v5667 (state s) (inputs i) = Zmod.unsigned (N.v5667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5667 s i)) at 1.
  unfold R.v5667, N.v5667.
  rewrite ?node_5598.
  rewrite ?node_5601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5668 (s : N.State) (i : N.Inputs) :
  R.v5668 (state s) (inputs i) = Zmod.unsigned (N.v5668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5668 s i)) at 1.
  unfold R.v5668, N.v5668.
  rewrite ?node_5666.
  rewrite ?node_5667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5669 (s : N.State) (i : N.Inputs) :
  R.v5669 (state s) (inputs i) = Zmod.unsigned (N.v5669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5669 s i)) at 1.
  unfold R.v5669, N.v5669.
  rewrite ?node_5665.
  rewrite ?node_5668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5670 (s : N.State) (i : N.Inputs) :
  R.v5670 (state s) (inputs i) = Zmod.unsigned (N.v5670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5670 s i)) at 1.
  unfold R.v5670, N.v5670.
  rewrite ?node_5602.
  rewrite ?node_5609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5671 (s : N.State) (i : N.Inputs) :
  R.v5671 (state s) (inputs i) = Zmod.unsigned (N.v5671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5671 s i)) at 1.
  unfold R.v5671, N.v5671.
  rewrite ?node_5610.
  rewrite ?node_5612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5672 (s : N.State) (i : N.Inputs) :
  R.v5672 (state s) (inputs i) = Zmod.unsigned (N.v5672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5672 s i)) at 1.
  unfold R.v5672, N.v5672.
  rewrite ?node_5670.
  rewrite ?node_5671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5673 (s : N.State) (i : N.Inputs) :
  R.v5673 (state s) (inputs i) = Zmod.unsigned (N.v5673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5673 s i)) at 1.
  unfold R.v5673, N.v5673.
  rewrite ?node_5669.
  rewrite ?node_5672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5674 (s : N.State) (i : N.Inputs) :
  R.v5674 (state s) (inputs i) = Zmod.unsigned (N.v5674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5674 s i)) at 1.
  unfold R.v5674, N.v5674.
  rewrite ?node_5604.
  rewrite !state_r126_nr_5F126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r126_nr_5F126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5675 (s : N.State) (i : N.Inputs) :
  R.v5675 (state s) (inputs i) = Zmod.unsigned (N.v5675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5675 s i)) at 1.
  unfold R.v5675, N.v5675.
  rewrite ?node_5605.
  rewrite ?node_5608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5676 (s : N.State) (i : N.Inputs) :
  R.v5676 (state s) (inputs i) = Zmod.unsigned (N.v5676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5676 s i)) at 1.
  unfold R.v5676, N.v5676.
  rewrite ?node_5674.
  rewrite ?node_5675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5677 (s : N.State) (i : N.Inputs) :
  R.v5677 (state s) (inputs i) = Zmod.unsigned (N.v5677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5677 s i)) at 1.
  unfold R.v5677, N.v5677.
  rewrite !state_r127_nr_5F127.
  rewrite !state_r128_nr_5F128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r127_nr_5F127 s)).
  rewrite ?(bits.mod_to_Z (N.r128_nr_5F128 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5678 (s : N.State) (i : N.Inputs) :
  R.v5678 (state s) (inputs i) = Zmod.unsigned (N.v5678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5678 s i)) at 1.
  unfold R.v5678, N.v5678.
  rewrite ?node_5611.
  rewrite !state_r129_nr_5F129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r129_nr_5F129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5679 (s : N.State) (i : N.Inputs) :
  R.v5679 (state s) (inputs i) = Zmod.unsigned (N.v5679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5679 s i)) at 1.
  unfold R.v5679, N.v5679.
  rewrite ?node_5677.
  rewrite ?node_5678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5680 (s : N.State) (i : N.Inputs) :
  R.v5680 (state s) (inputs i) = Zmod.unsigned (N.v5680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5680 s i)) at 1.
  unfold R.v5680, N.v5680.
  rewrite ?node_5676.
  rewrite ?node_5679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5681 (s : N.State) (i : N.Inputs) :
  R.v5681 (state s) (inputs i) = Zmod.unsigned (N.v5681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5681 s i)) at 1.
  unfold R.v5681, N.v5681.
  rewrite ?node_5673.
  rewrite ?node_5680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5682 (s : N.State) (i : N.Inputs) :
  R.v5682 (state s) (inputs i) = Zmod.unsigned (N.v5682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5682 s i)) at 1.
  unfold R.v5682, N.v5682.
  rewrite ?node_5613.
  rewrite ?node_5616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5683 (s : N.State) (i : N.Inputs) :
  R.v5683 (state s) (inputs i) = Zmod.unsigned (N.v5683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5683 s i)) at 1.
  unfold R.v5683, N.v5683.
  rewrite ?node_5617.
  rewrite ?node_5620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5684 (s : N.State) (i : N.Inputs) :
  R.v5684 (state s) (inputs i) = Zmod.unsigned (N.v5684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5684 s i)) at 1.
  unfold R.v5684, N.v5684.
  rewrite ?node_5682.
  rewrite ?node_5683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5685 (s : N.State) (i : N.Inputs) :
  R.v5685 (state s) (inputs i) = Zmod.unsigned (N.v5685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5685 s i)) at 1.
  unfold R.v5685, N.v5685.
  rewrite ?node_5681.
  rewrite ?node_5684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5686 (s : N.State) (i : N.Inputs) :
  R.v5686 (state s) (inputs i) = Zmod.unsigned (N.v5686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5686 s i)) at 1.
  unfold R.v5686, N.v5686.
  rewrite ?node_5624.
  rewrite ?node_5627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5687 (s : N.State) (i : N.Inputs) :
  R.v5687 (state s) (inputs i) = Zmod.unsigned (N.v5687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5687 s i)) at 1.
  unfold R.v5687, N.v5687.
  rewrite ?node_5685.
  rewrite ?node_5686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5688 (s : N.State) (i : N.Inputs) :
  R.v5688 (state s) (inputs i) = Zmod.unsigned (N.v5688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5688 s i)) at 1.
  unfold R.v5688, N.v5688.
  rewrite ?node_5621.
  rewrite ?node_5628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5689 (s : N.State) (i : N.Inputs) :
  R.v5689 (state s) (inputs i) = Zmod.unsigned (N.v5689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5689 s i)) at 1.
  unfold R.v5689, N.v5689.
  rewrite ?node_5629.
  rewrite ?node_5632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5690 (s : N.State) (i : N.Inputs) :
  R.v5690 (state s) (inputs i) = Zmod.unsigned (N.v5690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5690 s i)) at 1.
  unfold R.v5690, N.v5690.
  rewrite ?node_5688.
  rewrite ?node_5689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5691 (s : N.State) (i : N.Inputs) :
  R.v5691 (state s) (inputs i) = Zmod.unsigned (N.v5691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5691 s i)) at 1.
  unfold R.v5691, N.v5691.
  rewrite ?node_5687.
  rewrite ?node_5690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5692 (s : N.State) (i : N.Inputs) :
  R.v5692 (state s) (inputs i) = Zmod.unsigned (N.v5692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5692 s i)) at 1.
  unfold R.v5692, N.v5692.
  rewrite ?node_5633.
  rewrite ?node_5634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5693 (s : N.State) (i : N.Inputs) :
  R.v5693 (state s) (inputs i) = Zmod.unsigned (N.v5693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5693 s i)) at 1.
  unfold R.v5693, N.v5693.
  rewrite ?node_5635.
  rewrite ?node_5638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5694 (s : N.State) (i : N.Inputs) :
  R.v5694 (state s) (inputs i) = Zmod.unsigned (N.v5694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5694 s i)) at 1.
  unfold R.v5694, N.v5694.
  rewrite ?node_5692.
  rewrite ?node_5693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5695 (s : N.State) (i : N.Inputs) :
  R.v5695 (state s) (inputs i) = Zmod.unsigned (N.v5695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5695 s i)) at 1.
  unfold R.v5695, N.v5695.
  rewrite ?node_5691.
  rewrite ?node_5694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5696 (s : N.State) (i : N.Inputs) :
  R.v5696 (state s) (inputs i) = Zmod.unsigned (N.v5696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5696 s i)) at 1.
  unfold R.v5696, N.v5696.
  rewrite ?node_5639.
  rewrite ?node_5640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5697 (s : N.State) (i : N.Inputs) :
  R.v5697 (state s) (inputs i) = Zmod.unsigned (N.v5697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5697 s i)) at 1.
  unfold R.v5697, N.v5697.
  rewrite ?node_5695.
  rewrite ?node_5696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5698 (s : N.State) (i : N.Inputs) :
  R.v5698 (state s) (inputs i) = Zmod.unsigned (N.v5698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5698 s i)) at 1.
  unfold R.v5698, N.v5698.
  rewrite ?node_5697.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2313_nr_5F2344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2313_nr_5F2344 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5699 (s : N.State) (i : N.Inputs) :
  R.v5699 (state s) (inputs i) = Zmod.unsigned (N.v5699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5699 s i)) at 1.
  unfold R.v5699, N.v5699.
  rewrite ?node_5641.
  rewrite ?node_5642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5700 (s : N.State) (i : N.Inputs) :
  R.v5700 (state s) (inputs i) = Zmod.unsigned (N.v5700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5700 s i)) at 1.
  unfold R.v5700, N.v5700.
  rewrite ?node_5699.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2314_nr_5F2345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2314_nr_5F2345 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5701 (s : N.State) (i : N.Inputs) :
  R.v5701 (state s) (inputs i) = Zmod.unsigned (N.v5701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5701 s i)) at 1.
  unfold R.v5701, N.v5701.
  rewrite !state_r142_nr_5F142.
  rewrite !state_r143_nr_5F143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r142_nr_5F142 s)).
  rewrite ?(bits.mod_to_Z (N.r143_nr_5F143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5702 (s : N.State) (i : N.Inputs) :
  R.v5702 (state s) (inputs i) = Zmod.unsigned (N.v5702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5702 s i)) at 1.
  unfold R.v5702, N.v5702.
  rewrite ?node_5701.
  rewrite !state_r144_nr_5F144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r144_nr_5F144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5703 (s : N.State) (i : N.Inputs) :
  R.v5703 (state s) (inputs i) = Zmod.unsigned (N.v5703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5703 s i)) at 1.
  unfold R.v5703, N.v5703.
  rewrite ?node_5702.
  rewrite !state_r145_nr_5F145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r145_nr_5F145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5704 (s : N.State) (i : N.Inputs) :
  R.v5704 (state s) (inputs i) = Zmod.unsigned (N.v5704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5704 s i)) at 1.
  unfold R.v5704, N.v5704.
  rewrite !state_r130_nr_5F130.
  rewrite !state_r131_nr_5F131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r130_nr_5F130 s)).
  rewrite ?(bits.mod_to_Z (N.r131_nr_5F131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5705 (s : N.State) (i : N.Inputs) :
  R.v5705 (state s) (inputs i) = Zmod.unsigned (N.v5705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5705 s i)) at 1.
  unfold R.v5705, N.v5705.
  rewrite ?node_5647.
  rewrite !state_r132_nr_5F132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r132_nr_5F132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5706 (s : N.State) (i : N.Inputs) :
  R.v5706 (state s) (inputs i) = Zmod.unsigned (N.v5706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5706 s i)) at 1.
  unfold R.v5706, N.v5706.
  rewrite ?node_5704.
  rewrite ?node_5705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5707 (s : N.State) (i : N.Inputs) :
  R.v5707 (state s) (inputs i) = Zmod.unsigned (N.v5707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5707 s i)) at 1.
  unfold R.v5707, N.v5707.
  rewrite ?node_5703.
  rewrite ?node_5706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5708 (s : N.State) (i : N.Inputs) :
  R.v5708 (state s) (inputs i) = Zmod.unsigned (N.v5708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5708 s i)) at 1.
  unfold R.v5708, N.v5708.
  rewrite !state_r146_nr_5F146.
  rewrite !state_r147_nr_5F147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r146_nr_5F146 s)).
  rewrite ?(bits.mod_to_Z (N.r147_nr_5F147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5709 (s : N.State) (i : N.Inputs) :
  R.v5709 (state s) (inputs i) = Zmod.unsigned (N.v5709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5709 s i)) at 1.
  unfold R.v5709, N.v5709.
  rewrite ?node_5708.
  rewrite !state_r148_nr_5F148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r148_nr_5F148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5710 (s : N.State) (i : N.Inputs) :
  R.v5710 (state s) (inputs i) = Zmod.unsigned (N.v5710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5710 s i)) at 1.
  unfold R.v5710, N.v5710.
  rewrite ?node_5709.
  rewrite !state_r149_nr_5F149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r149_nr_5F149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5711 (s : N.State) (i : N.Inputs) :
  R.v5711 (state s) (inputs i) = Zmod.unsigned (N.v5711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5711 s i)) at 1.
  unfold R.v5711, N.v5711.
  rewrite !state_r134_nr_5F134.
  rewrite !state_r135_nr_5F135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r134_nr_5F134 s)).
  rewrite ?(bits.mod_to_Z (N.r135_nr_5F135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5712 (s : N.State) (i : N.Inputs) :
  R.v5712 (state s) (inputs i) = Zmod.unsigned (N.v5712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5712 s i)) at 1.
  unfold R.v5712, N.v5712.
  rewrite ?node_5654.
  rewrite !state_r136_nr_5F136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r136_nr_5F136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5713 (s : N.State) (i : N.Inputs) :
  R.v5713 (state s) (inputs i) = Zmod.unsigned (N.v5713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5713 s i)) at 1.
  unfold R.v5713, N.v5713.
  rewrite ?node_5711.
  rewrite ?node_5712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5714 (s : N.State) (i : N.Inputs) :
  R.v5714 (state s) (inputs i) = Zmod.unsigned (N.v5714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5714 s i)) at 1.
  unfold R.v5714, N.v5714.
  rewrite ?node_5710.
  rewrite ?node_5713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5715 (s : N.State) (i : N.Inputs) :
  R.v5715 (state s) (inputs i) = Zmod.unsigned (N.v5715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5715 s i)) at 1.
  unfold R.v5715, N.v5715.
  rewrite ?node_5707.
  rewrite ?node_5714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5716 (s : N.State) (i : N.Inputs) :
  R.v5716 (state s) (inputs i) = Zmod.unsigned (N.v5716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5716 s i)) at 1.
  unfold R.v5716, N.v5716.
  rewrite !state_r150_nr_5F150.
  rewrite !state_r151_nr_5F151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r150_nr_5F150 s)).
  rewrite ?(bits.mod_to_Z (N.r151_nr_5F151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5717 (s : N.State) (i : N.Inputs) :
  R.v5717 (state s) (inputs i) = Zmod.unsigned (N.v5717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5717 s i)) at 1.
  unfold R.v5717, N.v5717.
  rewrite ?node_5716.
  rewrite !state_r152_nr_5F152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r152_nr_5F152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5718 (s : N.State) (i : N.Inputs) :
  R.v5718 (state s) (inputs i) = Zmod.unsigned (N.v5718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5718 s i)) at 1.
  unfold R.v5718, N.v5718.
  rewrite ?node_5717.
  rewrite !state_r153_nr_5F153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r153_nr_5F153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5719 (s : N.State) (i : N.Inputs) :
  R.v5719 (state s) (inputs i) = Zmod.unsigned (N.v5719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5719 s i)) at 1.
  unfold R.v5719, N.v5719.
  rewrite !state_r138_nr_5F138.
  rewrite !state_r139_nr_5F139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r138_nr_5F138 s)).
  rewrite ?(bits.mod_to_Z (N.r139_nr_5F139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5720 (s : N.State) (i : N.Inputs) :
  R.v5720 (state s) (inputs i) = Zmod.unsigned (N.v5720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5720 s i)) at 1.
  unfold R.v5720, N.v5720.
  rewrite ?node_5662.
  rewrite !state_r140_nr_5F140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r140_nr_5F140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5721 (s : N.State) (i : N.Inputs) :
  R.v5721 (state s) (inputs i) = Zmod.unsigned (N.v5721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5721 s i)) at 1.
  unfold R.v5721, N.v5721.
  rewrite ?node_5719.
  rewrite ?node_5720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5722 (s : N.State) (i : N.Inputs) :
  R.v5722 (state s) (inputs i) = Zmod.unsigned (N.v5722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5722 s i)) at 1.
  unfold R.v5722, N.v5722.
  rewrite ?node_5718.
  rewrite ?node_5721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5723 (s : N.State) (i : N.Inputs) :
  R.v5723 (state s) (inputs i) = Zmod.unsigned (N.v5723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5723 s i)) at 1.
  unfold R.v5723, N.v5723.
  rewrite ?node_5715.
  rewrite ?node_5722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5724 (s : N.State) (i : N.Inputs) :
  R.v5724 (state s) (inputs i) = Zmod.unsigned (N.v5724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5724 s i)) at 1.
  unfold R.v5724, N.v5724.
  rewrite ?node_5648.
  rewrite !state_r133_nr_5F133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r133_nr_5F133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5725 (s : N.State) (i : N.Inputs) :
  R.v5725 (state s) (inputs i) = Zmod.unsigned (N.v5725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5725 s i)) at 1.
  unfold R.v5725, N.v5725.
  rewrite ?node_5649.
  rewrite ?node_5652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5726 (s : N.State) (i : N.Inputs) :
  R.v5726 (state s) (inputs i) = Zmod.unsigned (N.v5726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5726 s i)) at 1.
  unfold R.v5726, N.v5726.
  rewrite ?node_5724.
  rewrite ?node_5725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5727 (s : N.State) (i : N.Inputs) :
  R.v5727 (state s) (inputs i) = Zmod.unsigned (N.v5727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5727 s i)) at 1.
  unfold R.v5727, N.v5727.
  rewrite ?node_5723.
  rewrite ?node_5726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5728 (s : N.State) (i : N.Inputs) :
  R.v5728 (state s) (inputs i) = Zmod.unsigned (N.v5728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5728 s i)) at 1.
  unfold R.v5728, N.v5728.
  rewrite ?node_5653.
  rewrite ?node_5660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5729 (s : N.State) (i : N.Inputs) :
  R.v5729 (state s) (inputs i) = Zmod.unsigned (N.v5729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5729 s i)) at 1.
  unfold R.v5729, N.v5729.
  rewrite ?node_5661.
  rewrite ?node_5664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5730 (s : N.State) (i : N.Inputs) :
  R.v5730 (state s) (inputs i) = Zmod.unsigned (N.v5730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5730 s i)) at 1.
  unfold R.v5730, N.v5730.
  rewrite ?node_5728.
  rewrite ?node_5729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5731 (s : N.State) (i : N.Inputs) :
  R.v5731 (state s) (inputs i) = Zmod.unsigned (N.v5731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5731 s i)) at 1.
  unfold R.v5731, N.v5731.
  rewrite ?node_5727.
  rewrite ?node_5730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5732 (s : N.State) (i : N.Inputs) :
  R.v5732 (state s) (inputs i) = Zmod.unsigned (N.v5732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5732 s i)) at 1.
  unfold R.v5732, N.v5732.
  rewrite ?node_5655.
  rewrite !state_r137_nr_5F137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r137_nr_5F137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5733 (s : N.State) (i : N.Inputs) :
  R.v5733 (state s) (inputs i) = Zmod.unsigned (N.v5733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5733 s i)) at 1.
  unfold R.v5733, N.v5733.
  rewrite ?node_5656.
  rewrite ?node_5659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5734 (s : N.State) (i : N.Inputs) :
  R.v5734 (state s) (inputs i) = Zmod.unsigned (N.v5734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5734 s i)) at 1.
  unfold R.v5734, N.v5734.
  rewrite ?node_5732.
  rewrite ?node_5733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5735 (s : N.State) (i : N.Inputs) :
  R.v5735 (state s) (inputs i) = Zmod.unsigned (N.v5735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5735 s i)) at 1.
  unfold R.v5735, N.v5735.
  rewrite ?node_5663.
  rewrite !state_r141_nr_5F141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r141_nr_5F141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5736 (s : N.State) (i : N.Inputs) :
  R.v5736 (state s) (inputs i) = Zmod.unsigned (N.v5736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5736 s i)) at 1.
  unfold R.v5736, N.v5736.
  rewrite ?node_5734.
  rewrite ?node_5735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5737 (s : N.State) (i : N.Inputs) :
  R.v5737 (state s) (inputs i) = Zmod.unsigned (N.v5737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5737 s i)) at 1.
  unfold R.v5737, N.v5737.
  rewrite ?node_5731.
  rewrite ?node_5736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5738 (s : N.State) (i : N.Inputs) :
  R.v5738 (state s) (inputs i) = Zmod.unsigned (N.v5738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5738 s i)) at 1.
  unfold R.v5738, N.v5738.
  rewrite ?node_5665.
  rewrite ?node_5668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5739 (s : N.State) (i : N.Inputs) :
  R.v5739 (state s) (inputs i) = Zmod.unsigned (N.v5739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5739 s i)) at 1.
  unfold R.v5739, N.v5739.
  rewrite ?node_5669.
  rewrite ?node_5672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5740 (s : N.State) (i : N.Inputs) :
  R.v5740 (state s) (inputs i) = Zmod.unsigned (N.v5740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5740 s i)) at 1.
  unfold R.v5740, N.v5740.
  rewrite ?node_5738.
  rewrite ?node_5739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5741 (s : N.State) (i : N.Inputs) :
  R.v5741 (state s) (inputs i) = Zmod.unsigned (N.v5741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5741 s i)) at 1.
  unfold R.v5741, N.v5741.
  rewrite ?node_5737.
  rewrite ?node_5740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5742 (s : N.State) (i : N.Inputs) :
  R.v5742 (state s) (inputs i) = Zmod.unsigned (N.v5742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5742 s i)) at 1.
  unfold R.v5742, N.v5742.
  rewrite ?node_5676.
  rewrite ?node_5679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5743 (s : N.State) (i : N.Inputs) :
  R.v5743 (state s) (inputs i) = Zmod.unsigned (N.v5743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5743 s i)) at 1.
  unfold R.v5743, N.v5743.
  rewrite ?node_5741.
  rewrite ?node_5742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5744 (s : N.State) (i : N.Inputs) :
  R.v5744 (state s) (inputs i) = Zmod.unsigned (N.v5744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5744 s i)) at 1.
  unfold R.v5744, N.v5744.
  rewrite ?node_5673.
  rewrite ?node_5680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5745 (s : N.State) (i : N.Inputs) :
  R.v5745 (state s) (inputs i) = Zmod.unsigned (N.v5745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5745 s i)) at 1.
  unfold R.v5745, N.v5745.
  rewrite ?node_5681.
  rewrite ?node_5684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5746 (s : N.State) (i : N.Inputs) :
  R.v5746 (state s) (inputs i) = Zmod.unsigned (N.v5746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5746 s i)) at 1.
  unfold R.v5746, N.v5746.
  rewrite ?node_5744.
  rewrite ?node_5745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5747 (s : N.State) (i : N.Inputs) :
  R.v5747 (state s) (inputs i) = Zmod.unsigned (N.v5747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5747 s i)) at 1.
  unfold R.v5747, N.v5747.
  rewrite ?node_5743.
  rewrite ?node_5746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5748 (s : N.State) (i : N.Inputs) :
  R.v5748 (state s) (inputs i) = Zmod.unsigned (N.v5748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5748 s i)) at 1.
  unfold R.v5748, N.v5748.
  rewrite ?node_5685.
  rewrite ?node_5686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5749 (s : N.State) (i : N.Inputs) :
  R.v5749 (state s) (inputs i) = Zmod.unsigned (N.v5749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5749 s i)) at 1.
  unfold R.v5749, N.v5749.
  rewrite ?node_5687.
  rewrite ?node_5690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5750 (s : N.State) (i : N.Inputs) :
  R.v5750 (state s) (inputs i) = Zmod.unsigned (N.v5750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5750 s i)) at 1.
  unfold R.v5750, N.v5750.
  rewrite ?node_5748.
  rewrite ?node_5749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5751 (s : N.State) (i : N.Inputs) :
  R.v5751 (state s) (inputs i) = Zmod.unsigned (N.v5751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5751 s i)) at 1.
  unfold R.v5751, N.v5751.
  rewrite ?node_5747.
  rewrite ?node_5750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5752 (s : N.State) (i : N.Inputs) :
  R.v5752 (state s) (inputs i) = Zmod.unsigned (N.v5752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5752 s i)) at 1.
  unfold R.v5752, N.v5752.
  rewrite ?node_5691.
  rewrite ?node_5694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5753 (s : N.State) (i : N.Inputs) :
  R.v5753 (state s) (inputs i) = Zmod.unsigned (N.v5753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5753 s i)) at 1.
  unfold R.v5753, N.v5753.
  rewrite ?node_5751.
  rewrite ?node_5752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5754 (s : N.State) (i : N.Inputs) :
  R.v5754 (state s) (inputs i) = Zmod.unsigned (N.v5754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5754 s i)) at 1.
  unfold R.v5754, N.v5754.
  rewrite ?node_5753.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2315_nr_5F2346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2315_nr_5F2346 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5755 (s : N.State) (i : N.Inputs) :
  R.v5755 (state s) (inputs i) = Zmod.unsigned (N.v5755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5755 s i)) at 1.
  unfold R.v5755, N.v5755.
  rewrite ?node_5695.
  rewrite ?node_5696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5756 (s : N.State) (i : N.Inputs) :
  R.v5756 (state s) (inputs i) = Zmod.unsigned (N.v5756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5756 s i)) at 1.
  unfold R.v5756, N.v5756.
  rewrite ?node_5755.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2316_nr_5F2347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2316_nr_5F2347 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5757 (s : N.State) (i : N.Inputs) :
  R.v5757 (state s) (inputs i) = Zmod.unsigned (N.v5757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5757 s i)) at 1.
  unfold R.v5757, N.v5757.
  rewrite !state_r154_nr_5F154.
  rewrite !state_r155_nr_5F155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r154_nr_5F154 s)).
  rewrite ?(bits.mod_to_Z (N.r155_nr_5F155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5758 (s : N.State) (i : N.Inputs) :
  R.v5758 (state s) (inputs i) = Zmod.unsigned (N.v5758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5758 s i)) at 1.
  unfold R.v5758, N.v5758.
  rewrite ?node_5757.
  rewrite !state_r156_nr_5F156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r156_nr_5F156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5759 (s : N.State) (i : N.Inputs) :
  R.v5759 (state s) (inputs i) = Zmod.unsigned (N.v5759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5759 s i)) at 1.
  unfold R.v5759, N.v5759.
  rewrite ?node_5758.
  rewrite !state_r157_nr_5F157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r157_nr_5F157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5760 (s : N.State) (i : N.Inputs) :
  R.v5760 (state s) (inputs i) = Zmod.unsigned (N.v5760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5760 s i)) at 1.
  unfold R.v5760, N.v5760.
  rewrite !state_r142_nr_5F142.
  rewrite !state_r143_nr_5F143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r142_nr_5F142 s)).
  rewrite ?(bits.mod_to_Z (N.r143_nr_5F143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5761 (s : N.State) (i : N.Inputs) :
  R.v5761 (state s) (inputs i) = Zmod.unsigned (N.v5761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5761 s i)) at 1.
  unfold R.v5761, N.v5761.
  rewrite ?node_5701.
  rewrite !state_r144_nr_5F144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r144_nr_5F144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5762 (s : N.State) (i : N.Inputs) :
  R.v5762 (state s) (inputs i) = Zmod.unsigned (N.v5762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5762 s i)) at 1.
  unfold R.v5762, N.v5762.
  rewrite ?node_5760.
  rewrite ?node_5761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5763 (s : N.State) (i : N.Inputs) :
  R.v5763 (state s) (inputs i) = Zmod.unsigned (N.v5763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5763 s i)) at 1.
  unfold R.v5763, N.v5763.
  rewrite ?node_5759.
  rewrite ?node_5762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5764 (s : N.State) (i : N.Inputs) :
  R.v5764 (state s) (inputs i) = Zmod.unsigned (N.v5764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5764 s i)) at 1.
  unfold R.v5764, N.v5764.
  rewrite !state_r158_nr_5F158.
  rewrite !state_r159_nr_5F159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r158_nr_5F158 s)).
  rewrite ?(bits.mod_to_Z (N.r159_nr_5F159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5765 (s : N.State) (i : N.Inputs) :
  R.v5765 (state s) (inputs i) = Zmod.unsigned (N.v5765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5765 s i)) at 1.
  unfold R.v5765, N.v5765.
  rewrite ?node_5764.
  rewrite !state_r160_nr_5F160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r160_nr_5F160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5766 (s : N.State) (i : N.Inputs) :
  R.v5766 (state s) (inputs i) = Zmod.unsigned (N.v5766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5766 s i)) at 1.
  unfold R.v5766, N.v5766.
  rewrite ?node_5765.
  rewrite !state_r161_nr_5F161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r161_nr_5F161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5767 (s : N.State) (i : N.Inputs) :
  R.v5767 (state s) (inputs i) = Zmod.unsigned (N.v5767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5767 s i)) at 1.
  unfold R.v5767, N.v5767.
  rewrite !state_r146_nr_5F146.
  rewrite !state_r147_nr_5F147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r146_nr_5F146 s)).
  rewrite ?(bits.mod_to_Z (N.r147_nr_5F147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5768 (s : N.State) (i : N.Inputs) :
  R.v5768 (state s) (inputs i) = Zmod.unsigned (N.v5768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5768 s i)) at 1.
  unfold R.v5768, N.v5768.
  rewrite ?node_5708.
  rewrite !state_r148_nr_5F148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r148_nr_5F148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5769 (s : N.State) (i : N.Inputs) :
  R.v5769 (state s) (inputs i) = Zmod.unsigned (N.v5769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5769 s i)) at 1.
  unfold R.v5769, N.v5769.
  rewrite ?node_5767.
  rewrite ?node_5768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5770 (s : N.State) (i : N.Inputs) :
  R.v5770 (state s) (inputs i) = Zmod.unsigned (N.v5770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5770 s i)) at 1.
  unfold R.v5770, N.v5770.
  rewrite ?node_5766.
  rewrite ?node_5769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5771 (s : N.State) (i : N.Inputs) :
  R.v5771 (state s) (inputs i) = Zmod.unsigned (N.v5771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5771 s i)) at 1.
  unfold R.v5771, N.v5771.
  rewrite ?node_5763.
  rewrite ?node_5770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5772 (s : N.State) (i : N.Inputs) :
  R.v5772 (state s) (inputs i) = Zmod.unsigned (N.v5772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5772 s i)) at 1.
  unfold R.v5772, N.v5772.
  rewrite !state_r162_nr_5F162.
  rewrite !state_r163_nr_5F163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r162_nr_5F162 s)).
  rewrite ?(bits.mod_to_Z (N.r163_nr_5F163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5773 (s : N.State) (i : N.Inputs) :
  R.v5773 (state s) (inputs i) = Zmod.unsigned (N.v5773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5773 s i)) at 1.
  unfold R.v5773, N.v5773.
  rewrite ?node_5772.
  rewrite !state_r164_nr_5F164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r164_nr_5F164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5774 (s : N.State) (i : N.Inputs) :
  R.v5774 (state s) (inputs i) = Zmod.unsigned (N.v5774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5774 s i)) at 1.
  unfold R.v5774, N.v5774.
  rewrite ?node_5773.
  rewrite !state_r165_nr_5F165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r165_nr_5F165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5775 (s : N.State) (i : N.Inputs) :
  R.v5775 (state s) (inputs i) = Zmod.unsigned (N.v5775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5775 s i)) at 1.
  unfold R.v5775, N.v5775.
  rewrite !state_r150_nr_5F150.
  rewrite !state_r151_nr_5F151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r150_nr_5F150 s)).
  rewrite ?(bits.mod_to_Z (N.r151_nr_5F151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5776 (s : N.State) (i : N.Inputs) :
  R.v5776 (state s) (inputs i) = Zmod.unsigned (N.v5776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5776 s i)) at 1.
  unfold R.v5776, N.v5776.
  rewrite ?node_5716.
  rewrite !state_r152_nr_5F152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r152_nr_5F152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5777 (s : N.State) (i : N.Inputs) :
  R.v5777 (state s) (inputs i) = Zmod.unsigned (N.v5777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5777 s i)) at 1.
  unfold R.v5777, N.v5777.
  rewrite ?node_5775.
  rewrite ?node_5776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5778 (s : N.State) (i : N.Inputs) :
  R.v5778 (state s) (inputs i) = Zmod.unsigned (N.v5778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5778 s i)) at 1.
  unfold R.v5778, N.v5778.
  rewrite ?node_5774.
  rewrite ?node_5777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5779 (s : N.State) (i : N.Inputs) :
  R.v5779 (state s) (inputs i) = Zmod.unsigned (N.v5779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5779 s i)) at 1.
  unfold R.v5779, N.v5779.
  rewrite ?node_5771.
  rewrite ?node_5778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5780 (s : N.State) (i : N.Inputs) :
  R.v5780 (state s) (inputs i) = Zmod.unsigned (N.v5780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5780 s i)) at 1.
  unfold R.v5780, N.v5780.
  rewrite ?node_5779.
  rewrite !state_r166_nr_5F166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r166_nr_5F166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5781 (s : N.State) (i : N.Inputs) :
  R.v5781 (state s) (inputs i) = Zmod.unsigned (N.v5781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5781 s i)) at 1.
  unfold R.v5781, N.v5781.
  rewrite ?node_5707.
  rewrite ?node_5714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5782 (s : N.State) (i : N.Inputs) :
  R.v5782 (state s) (inputs i) = Zmod.unsigned (N.v5782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5782 s i)) at 1.
  unfold R.v5782, N.v5782.
  rewrite ?node_5715.
  rewrite ?node_5722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5783 (s : N.State) (i : N.Inputs) :
  R.v5783 (state s) (inputs i) = Zmod.unsigned (N.v5783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5783 s i)) at 1.
  unfold R.v5783, N.v5783.
  rewrite ?node_5781.
  rewrite ?node_5782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5784 (s : N.State) (i : N.Inputs) :
  R.v5784 (state s) (inputs i) = Zmod.unsigned (N.v5784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5784 s i)) at 1.
  unfold R.v5784, N.v5784.
  rewrite ?node_5780.
  rewrite ?node_5783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5785 (s : N.State) (i : N.Inputs) :
  R.v5785 (state s) (inputs i) = Zmod.unsigned (N.v5785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5785 s i)) at 1.
  unfold R.v5785, N.v5785.
  rewrite ?node_5702.
  rewrite !state_r145_nr_5F145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r145_nr_5F145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5786 (s : N.State) (i : N.Inputs) :
  R.v5786 (state s) (inputs i) = Zmod.unsigned (N.v5786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5786 s i)) at 1.
  unfold R.v5786, N.v5786.
  rewrite ?node_5703.
  rewrite ?node_5706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5787 (s : N.State) (i : N.Inputs) :
  R.v5787 (state s) (inputs i) = Zmod.unsigned (N.v5787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5787 s i)) at 1.
  unfold R.v5787, N.v5787.
  rewrite ?node_5785.
  rewrite ?node_5786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5788 (s : N.State) (i : N.Inputs) :
  R.v5788 (state s) (inputs i) = Zmod.unsigned (N.v5788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5788 s i)) at 1.
  unfold R.v5788, N.v5788.
  rewrite ?node_5709.
  rewrite !state_r149_nr_5F149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r149_nr_5F149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5789 (s : N.State) (i : N.Inputs) :
  R.v5789 (state s) (inputs i) = Zmod.unsigned (N.v5789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5789 s i)) at 1.
  unfold R.v5789, N.v5789.
  rewrite ?node_5710.
  rewrite ?node_5713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5790 (s : N.State) (i : N.Inputs) :
  R.v5790 (state s) (inputs i) = Zmod.unsigned (N.v5790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5790 s i)) at 1.
  unfold R.v5790, N.v5790.
  rewrite ?node_5788.
  rewrite ?node_5789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5791 (s : N.State) (i : N.Inputs) :
  R.v5791 (state s) (inputs i) = Zmod.unsigned (N.v5791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5791 s i)) at 1.
  unfold R.v5791, N.v5791.
  rewrite ?node_5787.
  rewrite ?node_5790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5792 (s : N.State) (i : N.Inputs) :
  R.v5792 (state s) (inputs i) = Zmod.unsigned (N.v5792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5792 s i)) at 1.
  unfold R.v5792, N.v5792.
  rewrite ?node_5717.
  rewrite !state_r153_nr_5F153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r153_nr_5F153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5793 (s : N.State) (i : N.Inputs) :
  R.v5793 (state s) (inputs i) = Zmod.unsigned (N.v5793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5793 s i)) at 1.
  unfold R.v5793, N.v5793.
  rewrite ?node_5718.
  rewrite ?node_5721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5794 (s : N.State) (i : N.Inputs) :
  R.v5794 (state s) (inputs i) = Zmod.unsigned (N.v5794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5794 s i)) at 1.
  unfold R.v5794, N.v5794.
  rewrite ?node_5792.
  rewrite ?node_5793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5795 (s : N.State) (i : N.Inputs) :
  R.v5795 (state s) (inputs i) = Zmod.unsigned (N.v5795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5795 s i)) at 1.
  unfold R.v5795, N.v5795.
  rewrite ?node_5791.
  rewrite ?node_5794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5796 (s : N.State) (i : N.Inputs) :
  R.v5796 (state s) (inputs i) = Zmod.unsigned (N.v5796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5796 s i)) at 1.
  unfold R.v5796, N.v5796.
  rewrite ?node_5784.
  rewrite ?node_5795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5797 (s : N.State) (i : N.Inputs) :
  R.v5797 (state s) (inputs i) = Zmod.unsigned (N.v5797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5797 s i)) at 1.
  unfold R.v5797, N.v5797.
  rewrite ?node_5723.
  rewrite ?node_5726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5798 (s : N.State) (i : N.Inputs) :
  R.v5798 (state s) (inputs i) = Zmod.unsigned (N.v5798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5798 s i)) at 1.
  unfold R.v5798, N.v5798.
  rewrite ?node_5727.
  rewrite ?node_5730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5799 (s : N.State) (i : N.Inputs) :
  R.v5799 (state s) (inputs i) = Zmod.unsigned (N.v5799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5799 s i)) at 1.
  unfold R.v5799, N.v5799.
  rewrite ?node_5797.
  rewrite ?node_5798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5800 (s : N.State) (i : N.Inputs) :
  R.v5800 (state s) (inputs i) = Zmod.unsigned (N.v5800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5800 s i)) at 1.
  unfold R.v5800, N.v5800.
  rewrite ?node_5796.
  rewrite ?node_5799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5801 (s : N.State) (i : N.Inputs) :
  R.v5801 (state s) (inputs i) = Zmod.unsigned (N.v5801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5801 s i)) at 1.
  unfold R.v5801, N.v5801.
  rewrite ?node_5734.
  rewrite ?node_5735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5802 (s : N.State) (i : N.Inputs) :
  R.v5802 (state s) (inputs i) = Zmod.unsigned (N.v5802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5802 s i)) at 1.
  unfold R.v5802, N.v5802.
  rewrite ?node_5800.
  rewrite ?node_5801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5803 (s : N.State) (i : N.Inputs) :
  R.v5803 (state s) (inputs i) = Zmod.unsigned (N.v5803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5803 s i)) at 1.
  unfold R.v5803, N.v5803.
  rewrite ?node_5731.
  rewrite ?node_5736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5804 (s : N.State) (i : N.Inputs) :
  R.v5804 (state s) (inputs i) = Zmod.unsigned (N.v5804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5804 s i)) at 1.
  unfold R.v5804, N.v5804.
  rewrite ?node_5737.
  rewrite ?node_5740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5805 (s : N.State) (i : N.Inputs) :
  R.v5805 (state s) (inputs i) = Zmod.unsigned (N.v5805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5805 s i)) at 1.
  unfold R.v5805, N.v5805.
  rewrite ?node_5803.
  rewrite ?node_5804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5806 (s : N.State) (i : N.Inputs) :
  R.v5806 (state s) (inputs i) = Zmod.unsigned (N.v5806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5806 s i)) at 1.
  unfold R.v5806, N.v5806.
  rewrite ?node_5802.
  rewrite ?node_5805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5807 (s : N.State) (i : N.Inputs) :
  R.v5807 (state s) (inputs i) = Zmod.unsigned (N.v5807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5807 s i)) at 1.
  unfold R.v5807, N.v5807.
  rewrite ?node_5741.
  rewrite ?node_5742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5808 (s : N.State) (i : N.Inputs) :
  R.v5808 (state s) (inputs i) = Zmod.unsigned (N.v5808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5808 s i)) at 1.
  unfold R.v5808, N.v5808.
  rewrite ?node_5743.
  rewrite ?node_5746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5809 (s : N.State) (i : N.Inputs) :
  R.v5809 (state s) (inputs i) = Zmod.unsigned (N.v5809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5809 s i)) at 1.
  unfold R.v5809, N.v5809.
  rewrite ?node_5807.
  rewrite ?node_5808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5810 (s : N.State) (i : N.Inputs) :
  R.v5810 (state s) (inputs i) = Zmod.unsigned (N.v5810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5810 s i)) at 1.
  unfold R.v5810, N.v5810.
  rewrite ?node_5806.
  rewrite ?node_5809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5811 (s : N.State) (i : N.Inputs) :
  R.v5811 (state s) (inputs i) = Zmod.unsigned (N.v5811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5811 s i)) at 1.
  unfold R.v5811, N.v5811.
  rewrite ?node_5747.
  rewrite ?node_5750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5812 (s : N.State) (i : N.Inputs) :
  R.v5812 (state s) (inputs i) = Zmod.unsigned (N.v5812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5812 s i)) at 1.
  unfold R.v5812, N.v5812.
  rewrite ?node_5810.
  rewrite ?node_5811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5813 (s : N.State) (i : N.Inputs) :
  R.v5813 (state s) (inputs i) = Zmod.unsigned (N.v5813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5813 s i)) at 1.
  unfold R.v5813, N.v5813.
  rewrite ?node_5812.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2317_nr_5F2348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2317_nr_5F2348 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5814 (s : N.State) (i : N.Inputs) :
  R.v5814 (state s) (inputs i) = Zmod.unsigned (N.v5814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5814 s i)) at 1.
  unfold R.v5814, N.v5814.
  rewrite ?node_5751.
  rewrite ?node_5752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5815 (s : N.State) (i : N.Inputs) :
  R.v5815 (state s) (inputs i) = Zmod.unsigned (N.v5815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5815 s i)) at 1.
  unfold R.v5815, N.v5815.
  rewrite ?node_5814.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2318_nr_5F2349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2318_nr_5F2349 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5816 (s : N.State) (i : N.Inputs) :
  R.v5816 (state s) (inputs i) = Zmod.unsigned (N.v5816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5816 s i)) at 1.
  unfold R.v5816, N.v5816.
  rewrite !state_r167_nr_5F167.
  rewrite !state_r168_nr_5F168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r167_nr_5F167 s)).
  rewrite ?(bits.mod_to_Z (N.r168_nr_5F168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5817 (s : N.State) (i : N.Inputs) :
  R.v5817 (state s) (inputs i) = Zmod.unsigned (N.v5817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5817 s i)) at 1.
  unfold R.v5817, N.v5817.
  rewrite ?node_5816.
  rewrite !state_r169_nr_5F169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r169_nr_5F169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5818 (s : N.State) (i : N.Inputs) :
  R.v5818 (state s) (inputs i) = Zmod.unsigned (N.v5818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5818 s i)) at 1.
  unfold R.v5818, N.v5818.
  rewrite ?node_5817.
  rewrite !state_r170_nr_5F170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r170_nr_5F170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5819 (s : N.State) (i : N.Inputs) :
  R.v5819 (state s) (inputs i) = Zmod.unsigned (N.v5819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5819 s i)) at 1.
  unfold R.v5819, N.v5819.
  rewrite !state_r154_nr_5F154.
  rewrite !state_r155_nr_5F155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r154_nr_5F154 s)).
  rewrite ?(bits.mod_to_Z (N.r155_nr_5F155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5820 (s : N.State) (i : N.Inputs) :
  R.v5820 (state s) (inputs i) = Zmod.unsigned (N.v5820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5820 s i)) at 1.
  unfold R.v5820, N.v5820.
  rewrite ?node_5757.
  rewrite !state_r156_nr_5F156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r156_nr_5F156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5821 (s : N.State) (i : N.Inputs) :
  R.v5821 (state s) (inputs i) = Zmod.unsigned (N.v5821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5821 s i)) at 1.
  unfold R.v5821, N.v5821.
  rewrite ?node_5819.
  rewrite ?node_5820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5822 (s : N.State) (i : N.Inputs) :
  R.v5822 (state s) (inputs i) = Zmod.unsigned (N.v5822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5822 s i)) at 1.
  unfold R.v5822, N.v5822.
  rewrite ?node_5818.
  rewrite ?node_5821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5823 (s : N.State) (i : N.Inputs) :
  R.v5823 (state s) (inputs i) = Zmod.unsigned (N.v5823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5823 s i)) at 1.
  unfold R.v5823, N.v5823.
  rewrite !state_r171_nr_5F171.
  rewrite !state_r172_nr_5F172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r171_nr_5F171 s)).
  rewrite ?(bits.mod_to_Z (N.r172_nr_5F172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5824 (s : N.State) (i : N.Inputs) :
  R.v5824 (state s) (inputs i) = Zmod.unsigned (N.v5824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5824 s i)) at 1.
  unfold R.v5824, N.v5824.
  rewrite ?node_5823.
  rewrite !state_r173_nr_5F173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r173_nr_5F173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5825 (s : N.State) (i : N.Inputs) :
  R.v5825 (state s) (inputs i) = Zmod.unsigned (N.v5825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5825 s i)) at 1.
  unfold R.v5825, N.v5825.
  rewrite ?node_5824.
  rewrite !state_r174_nr_5F174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r174_nr_5F174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5826 (s : N.State) (i : N.Inputs) :
  R.v5826 (state s) (inputs i) = Zmod.unsigned (N.v5826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5826 s i)) at 1.
  unfold R.v5826, N.v5826.
  rewrite !state_r158_nr_5F158.
  rewrite !state_r159_nr_5F159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r158_nr_5F158 s)).
  rewrite ?(bits.mod_to_Z (N.r159_nr_5F159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5827 (s : N.State) (i : N.Inputs) :
  R.v5827 (state s) (inputs i) = Zmod.unsigned (N.v5827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5827 s i)) at 1.
  unfold R.v5827, N.v5827.
  rewrite ?node_5764.
  rewrite !state_r160_nr_5F160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r160_nr_5F160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5828 (s : N.State) (i : N.Inputs) :
  R.v5828 (state s) (inputs i) = Zmod.unsigned (N.v5828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5828 s i)) at 1.
  unfold R.v5828, N.v5828.
  rewrite ?node_5826.
  rewrite ?node_5827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5829 (s : N.State) (i : N.Inputs) :
  R.v5829 (state s) (inputs i) = Zmod.unsigned (N.v5829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5829 s i)) at 1.
  unfold R.v5829, N.v5829.
  rewrite ?node_5825.
  rewrite ?node_5828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5830 (s : N.State) (i : N.Inputs) :
  R.v5830 (state s) (inputs i) = Zmod.unsigned (N.v5830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5830 s i)) at 1.
  unfold R.v5830, N.v5830.
  rewrite ?node_5822.
  rewrite ?node_5829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5831 (s : N.State) (i : N.Inputs) :
  R.v5831 (state s) (inputs i) = Zmod.unsigned (N.v5831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5831 s i)) at 1.
  unfold R.v5831, N.v5831.
  rewrite !state_r175_nr_5F175.
  rewrite !state_r176_nr_5F176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r175_nr_5F175 s)).
  rewrite ?(bits.mod_to_Z (N.r176_nr_5F176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5832 (s : N.State) (i : N.Inputs) :
  R.v5832 (state s) (inputs i) = Zmod.unsigned (N.v5832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5832 s i)) at 1.
  unfold R.v5832, N.v5832.
  rewrite ?node_5831.
  rewrite !state_r177_nr_5F177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r177_nr_5F177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5833 (s : N.State) (i : N.Inputs) :
  R.v5833 (state s) (inputs i) = Zmod.unsigned (N.v5833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5833 s i)) at 1.
  unfold R.v5833, N.v5833.
  rewrite ?node_5832.
  rewrite !state_r178_nr_5F178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r178_nr_5F178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5834 (s : N.State) (i : N.Inputs) :
  R.v5834 (state s) (inputs i) = Zmod.unsigned (N.v5834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5834 s i)) at 1.
  unfold R.v5834, N.v5834.
  rewrite !state_r162_nr_5F162.
  rewrite !state_r163_nr_5F163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r162_nr_5F162 s)).
  rewrite ?(bits.mod_to_Z (N.r163_nr_5F163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5835 (s : N.State) (i : N.Inputs) :
  R.v5835 (state s) (inputs i) = Zmod.unsigned (N.v5835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5835 s i)) at 1.
  unfold R.v5835, N.v5835.
  rewrite ?node_5772.
  rewrite !state_r164_nr_5F164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r164_nr_5F164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5836 (s : N.State) (i : N.Inputs) :
  R.v5836 (state s) (inputs i) = Zmod.unsigned (N.v5836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5836 s i)) at 1.
  unfold R.v5836, N.v5836.
  rewrite ?node_5834.
  rewrite ?node_5835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5837 (s : N.State) (i : N.Inputs) :
  R.v5837 (state s) (inputs i) = Zmod.unsigned (N.v5837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5837 s i)) at 1.
  unfold R.v5837, N.v5837.
  rewrite ?node_5833.
  rewrite ?node_5836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5838 (s : N.State) (i : N.Inputs) :
  R.v5838 (state s) (inputs i) = Zmod.unsigned (N.v5838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5838 s i)) at 1.
  unfold R.v5838, N.v5838.
  rewrite ?node_5830.
  rewrite ?node_5837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5839 (s : N.State) (i : N.Inputs) :
  R.v5839 (state s) (inputs i) = Zmod.unsigned (N.v5839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5839 s i)) at 1.
  unfold R.v5839, N.v5839.
  rewrite ?node_5838.
  rewrite !state_r179_nr_5F179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r179_nr_5F179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5840 (s : N.State) (i : N.Inputs) :
  R.v5840 (state s) (inputs i) = Zmod.unsigned (N.v5840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5840 s i)) at 1.
  unfold R.v5840, N.v5840.
  rewrite ?node_5763.
  rewrite ?node_5770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5841 (s : N.State) (i : N.Inputs) :
  R.v5841 (state s) (inputs i) = Zmod.unsigned (N.v5841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5841 s i)) at 1.
  unfold R.v5841, N.v5841.
  rewrite ?node_5771.
  rewrite ?node_5778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5842 (s : N.State) (i : N.Inputs) :
  R.v5842 (state s) (inputs i) = Zmod.unsigned (N.v5842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5842 s i)) at 1.
  unfold R.v5842, N.v5842.
  rewrite ?node_5840.
  rewrite ?node_5841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5843 (s : N.State) (i : N.Inputs) :
  R.v5843 (state s) (inputs i) = Zmod.unsigned (N.v5843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5843 s i)) at 1.
  unfold R.v5843, N.v5843.
  rewrite ?node_5839.
  rewrite ?node_5842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5844 (s : N.State) (i : N.Inputs) :
  R.v5844 (state s) (inputs i) = Zmod.unsigned (N.v5844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5844 s i)) at 1.
  unfold R.v5844, N.v5844.
  rewrite ?node_5758.
  rewrite !state_r157_nr_5F157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r157_nr_5F157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5845 (s : N.State) (i : N.Inputs) :
  R.v5845 (state s) (inputs i) = Zmod.unsigned (N.v5845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5845 s i)) at 1.
  unfold R.v5845, N.v5845.
  rewrite ?node_5759.
  rewrite ?node_5762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5846 (s : N.State) (i : N.Inputs) :
  R.v5846 (state s) (inputs i) = Zmod.unsigned (N.v5846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5846 s i)) at 1.
  unfold R.v5846, N.v5846.
  rewrite ?node_5844.
  rewrite ?node_5845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5847 (s : N.State) (i : N.Inputs) :
  R.v5847 (state s) (inputs i) = Zmod.unsigned (N.v5847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5847 s i)) at 1.
  unfold R.v5847, N.v5847.
  rewrite ?node_5765.
  rewrite !state_r161_nr_5F161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r161_nr_5F161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5848 (s : N.State) (i : N.Inputs) :
  R.v5848 (state s) (inputs i) = Zmod.unsigned (N.v5848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5848 s i)) at 1.
  unfold R.v5848, N.v5848.
  rewrite ?node_5766.
  rewrite ?node_5769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5849 (s : N.State) (i : N.Inputs) :
  R.v5849 (state s) (inputs i) = Zmod.unsigned (N.v5849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5849 s i)) at 1.
  unfold R.v5849, N.v5849.
  rewrite ?node_5847.
  rewrite ?node_5848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5850 (s : N.State) (i : N.Inputs) :
  R.v5850 (state s) (inputs i) = Zmod.unsigned (N.v5850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5850 s i)) at 1.
  unfold R.v5850, N.v5850.
  rewrite ?node_5846.
  rewrite ?node_5849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5851 (s : N.State) (i : N.Inputs) :
  R.v5851 (state s) (inputs i) = Zmod.unsigned (N.v5851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5851 s i)) at 1.
  unfold R.v5851, N.v5851.
  rewrite ?node_5773.
  rewrite !state_r165_nr_5F165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r165_nr_5F165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5852 (s : N.State) (i : N.Inputs) :
  R.v5852 (state s) (inputs i) = Zmod.unsigned (N.v5852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5852 s i)) at 1.
  unfold R.v5852, N.v5852.
  rewrite ?node_5774.
  rewrite ?node_5777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5853 (s : N.State) (i : N.Inputs) :
  R.v5853 (state s) (inputs i) = Zmod.unsigned (N.v5853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5853 s i)) at 1.
  unfold R.v5853, N.v5853.
  rewrite ?node_5851.
  rewrite ?node_5852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5854 (s : N.State) (i : N.Inputs) :
  R.v5854 (state s) (inputs i) = Zmod.unsigned (N.v5854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5854 s i)) at 1.
  unfold R.v5854, N.v5854.
  rewrite ?node_5850.
  rewrite ?node_5853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5855 (s : N.State) (i : N.Inputs) :
  R.v5855 (state s) (inputs i) = Zmod.unsigned (N.v5855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5855 s i)) at 1.
  unfold R.v5855, N.v5855.
  rewrite ?node_5843.
  rewrite ?node_5854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5856 (s : N.State) (i : N.Inputs) :
  R.v5856 (state s) (inputs i) = Zmod.unsigned (N.v5856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5856 s i)) at 1.
  unfold R.v5856, N.v5856.
  rewrite ?node_5779.
  rewrite !state_r166_nr_5F166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r166_nr_5F166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5857 (s : N.State) (i : N.Inputs) :
  R.v5857 (state s) (inputs i) = Zmod.unsigned (N.v5857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5857 s i)) at 1.
  unfold R.v5857, N.v5857.
  rewrite ?node_5780.
  rewrite ?node_5783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5858 (s : N.State) (i : N.Inputs) :
  R.v5858 (state s) (inputs i) = Zmod.unsigned (N.v5858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5858 s i)) at 1.
  unfold R.v5858, N.v5858.
  rewrite ?node_5856.
  rewrite ?node_5857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5859 (s : N.State) (i : N.Inputs) :
  R.v5859 (state s) (inputs i) = Zmod.unsigned (N.v5859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5859 s i)) at 1.
  unfold R.v5859, N.v5859.
  rewrite ?node_5855.
  rewrite ?node_5858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5860 (s : N.State) (i : N.Inputs) :
  R.v5860 (state s) (inputs i) = Zmod.unsigned (N.v5860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5860 s i)) at 1.
  unfold R.v5860, N.v5860.
  rewrite ?node_5787.
  rewrite ?node_5790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5861 (s : N.State) (i : N.Inputs) :
  R.v5861 (state s) (inputs i) = Zmod.unsigned (N.v5861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5861 s i)) at 1.
  unfold R.v5861, N.v5861.
  rewrite ?node_5791.
  rewrite ?node_5794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5862 (s : N.State) (i : N.Inputs) :
  R.v5862 (state s) (inputs i) = Zmod.unsigned (N.v5862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5862 s i)) at 1.
  unfold R.v5862, N.v5862.
  rewrite ?node_5860.
  rewrite ?node_5861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5863 (s : N.State) (i : N.Inputs) :
  R.v5863 (state s) (inputs i) = Zmod.unsigned (N.v5863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5863 s i)) at 1.
  unfold R.v5863, N.v5863.
  rewrite ?node_5859.
  rewrite ?node_5862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5864 (s : N.State) (i : N.Inputs) :
  R.v5864 (state s) (inputs i) = Zmod.unsigned (N.v5864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5864 s i)) at 1.
  unfold R.v5864, N.v5864.
  rewrite ?node_5784.
  rewrite ?node_5795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5865 (s : N.State) (i : N.Inputs) :
  R.v5865 (state s) (inputs i) = Zmod.unsigned (N.v5865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5865 s i)) at 1.
  unfold R.v5865, N.v5865.
  rewrite ?node_5796.
  rewrite ?node_5799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5866 (s : N.State) (i : N.Inputs) :
  R.v5866 (state s) (inputs i) = Zmod.unsigned (N.v5866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5866 s i)) at 1.
  unfold R.v5866, N.v5866.
  rewrite ?node_5864.
  rewrite ?node_5865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5867 (s : N.State) (i : N.Inputs) :
  R.v5867 (state s) (inputs i) = Zmod.unsigned (N.v5867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5867 s i)) at 1.
  unfold R.v5867, N.v5867.
  rewrite ?node_5863.
  rewrite ?node_5866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5868 (s : N.State) (i : N.Inputs) :
  R.v5868 (state s) (inputs i) = Zmod.unsigned (N.v5868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5868 s i)) at 1.
  unfold R.v5868, N.v5868.
  rewrite ?node_5800.
  rewrite ?node_5801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5869 (s : N.State) (i : N.Inputs) :
  R.v5869 (state s) (inputs i) = Zmod.unsigned (N.v5869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5869 s i)) at 1.
  unfold R.v5869, N.v5869.
  rewrite ?node_5802.
  rewrite ?node_5805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5870 (s : N.State) (i : N.Inputs) :
  R.v5870 (state s) (inputs i) = Zmod.unsigned (N.v5870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5870 s i)) at 1.
  unfold R.v5870, N.v5870.
  rewrite ?node_5868.
  rewrite ?node_5869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5871 (s : N.State) (i : N.Inputs) :
  R.v5871 (state s) (inputs i) = Zmod.unsigned (N.v5871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5871 s i)) at 1.
  unfold R.v5871, N.v5871.
  rewrite ?node_5867.
  rewrite ?node_5870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5872 (s : N.State) (i : N.Inputs) :
  R.v5872 (state s) (inputs i) = Zmod.unsigned (N.v5872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5872 s i)) at 1.
  unfold R.v5872, N.v5872.
  rewrite ?node_5806.
  rewrite ?node_5809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5873 (s : N.State) (i : N.Inputs) :
  R.v5873 (state s) (inputs i) = Zmod.unsigned (N.v5873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5873 s i)) at 1.
  unfold R.v5873, N.v5873.
  rewrite ?node_5871.
  rewrite ?node_5872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5874 (s : N.State) (i : N.Inputs) :
  R.v5874 (state s) (inputs i) = Zmod.unsigned (N.v5874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5874 s i)) at 1.
  unfold R.v5874, N.v5874.
  rewrite ?node_5873.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2319_nr_5F2350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2319_nr_5F2350 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5875 (s : N.State) (i : N.Inputs) :
  R.v5875 (state s) (inputs i) = Zmod.unsigned (N.v5875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5875 s i)) at 1.
  unfold R.v5875, N.v5875.
  rewrite ?node_5810.
  rewrite ?node_5811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5876 (s : N.State) (i : N.Inputs) :
  R.v5876 (state s) (inputs i) = Zmod.unsigned (N.v5876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5876 s i)) at 1.
  unfold R.v5876, N.v5876.
  rewrite ?node_5875.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2320_nr_5F2351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2320_nr_5F2351 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5877 (s : N.State) (i : N.Inputs) :
  R.v5877 (state s) (inputs i) = Zmod.unsigned (N.v5877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5877 s i)) at 1.
  unfold R.v5877, N.v5877.
  rewrite !state_r180_nr_5F180.
  rewrite !state_r181_nr_5F181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r180_nr_5F180 s)).
  rewrite ?(bits.mod_to_Z (N.r181_nr_5F181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5878 (s : N.State) (i : N.Inputs) :
  R.v5878 (state s) (inputs i) = Zmod.unsigned (N.v5878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5878 s i)) at 1.
  unfold R.v5878, N.v5878.
  rewrite ?node_5877.
  rewrite !state_r182_nr_5F182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r182_nr_5F182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5879 (s : N.State) (i : N.Inputs) :
  R.v5879 (state s) (inputs i) = Zmod.unsigned (N.v5879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5879 s i)) at 1.
  unfold R.v5879, N.v5879.
  rewrite ?node_5878.
  rewrite !state_r183_nr_5F183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r183_nr_5F183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5880 (s : N.State) (i : N.Inputs) :
  R.v5880 (state s) (inputs i) = Zmod.unsigned (N.v5880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5880 s i)) at 1.
  unfold R.v5880, N.v5880.
  rewrite !state_r167_nr_5F167.
  rewrite !state_r168_nr_5F168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r167_nr_5F167 s)).
  rewrite ?(bits.mod_to_Z (N.r168_nr_5F168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5881 (s : N.State) (i : N.Inputs) :
  R.v5881 (state s) (inputs i) = Zmod.unsigned (N.v5881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5881 s i)) at 1.
  unfold R.v5881, N.v5881.
  rewrite ?node_5816.
  rewrite !state_r169_nr_5F169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r169_nr_5F169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5882 (s : N.State) (i : N.Inputs) :
  R.v5882 (state s) (inputs i) = Zmod.unsigned (N.v5882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5882 s i)) at 1.
  unfold R.v5882, N.v5882.
  rewrite ?node_5880.
  rewrite ?node_5881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5883 (s : N.State) (i : N.Inputs) :
  R.v5883 (state s) (inputs i) = Zmod.unsigned (N.v5883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5883 s i)) at 1.
  unfold R.v5883, N.v5883.
  rewrite ?node_5879.
  rewrite ?node_5882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5884 (s : N.State) (i : N.Inputs) :
  R.v5884 (state s) (inputs i) = Zmod.unsigned (N.v5884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5884 s i)) at 1.
  unfold R.v5884, N.v5884.
  rewrite !state_r184_nr_5F184.
  rewrite !state_r185_nr_5F185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r184_nr_5F184 s)).
  rewrite ?(bits.mod_to_Z (N.r185_nr_5F185 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5885 (s : N.State) (i : N.Inputs) :
  R.v5885 (state s) (inputs i) = Zmod.unsigned (N.v5885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5885 s i)) at 1.
  unfold R.v5885, N.v5885.
  rewrite ?node_5884.
  rewrite !state_r186_nr_5F186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r186_nr_5F186 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5886 (s : N.State) (i : N.Inputs) :
  R.v5886 (state s) (inputs i) = Zmod.unsigned (N.v5886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5886 s i)) at 1.
  unfold R.v5886, N.v5886.
  rewrite ?node_5885.
  rewrite !state_r187_nr_5F187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r187_nr_5F187 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5887 (s : N.State) (i : N.Inputs) :
  R.v5887 (state s) (inputs i) = Zmod.unsigned (N.v5887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5887 s i)) at 1.
  unfold R.v5887, N.v5887.
  rewrite !state_r171_nr_5F171.
  rewrite !state_r172_nr_5F172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r171_nr_5F171 s)).
  rewrite ?(bits.mod_to_Z (N.r172_nr_5F172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5888 (s : N.State) (i : N.Inputs) :
  R.v5888 (state s) (inputs i) = Zmod.unsigned (N.v5888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5888 s i)) at 1.
  unfold R.v5888, N.v5888.
  rewrite ?node_5823.
  rewrite !state_r173_nr_5F173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r173_nr_5F173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5889 (s : N.State) (i : N.Inputs) :
  R.v5889 (state s) (inputs i) = Zmod.unsigned (N.v5889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5889 s i)) at 1.
  unfold R.v5889, N.v5889.
  rewrite ?node_5887.
  rewrite ?node_5888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5890 (s : N.State) (i : N.Inputs) :
  R.v5890 (state s) (inputs i) = Zmod.unsigned (N.v5890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5890 s i)) at 1.
  unfold R.v5890, N.v5890.
  rewrite ?node_5886.
  rewrite ?node_5889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5891 (s : N.State) (i : N.Inputs) :
  R.v5891 (state s) (inputs i) = Zmod.unsigned (N.v5891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5891 s i)) at 1.
  unfold R.v5891, N.v5891.
  rewrite ?node_5883.
  rewrite ?node_5890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5892 (s : N.State) (i : N.Inputs) :
  R.v5892 (state s) (inputs i) = Zmod.unsigned (N.v5892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5892 s i)) at 1.
  unfold R.v5892, N.v5892.
  rewrite !state_r188_nr_5F188.
  rewrite !state_r189_nr_5F189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r188_nr_5F188 s)).
  rewrite ?(bits.mod_to_Z (N.r189_nr_5F189 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5893 (s : N.State) (i : N.Inputs) :
  R.v5893 (state s) (inputs i) = Zmod.unsigned (N.v5893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5893 s i)) at 1.
  unfold R.v5893, N.v5893.
  rewrite ?node_5892.
  rewrite !state_r190_nr_5F190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r190_nr_5F190 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5894 (s : N.State) (i : N.Inputs) :
  R.v5894 (state s) (inputs i) = Zmod.unsigned (N.v5894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5894 s i)) at 1.
  unfold R.v5894, N.v5894.
  rewrite ?node_5893.
  rewrite !state_r191_nr_5F191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r191_nr_5F191 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5895 (s : N.State) (i : N.Inputs) :
  R.v5895 (state s) (inputs i) = Zmod.unsigned (N.v5895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5895 s i)) at 1.
  unfold R.v5895, N.v5895.
  rewrite !state_r175_nr_5F175.
  rewrite !state_r176_nr_5F176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r175_nr_5F175 s)).
  rewrite ?(bits.mod_to_Z (N.r176_nr_5F176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5896 (s : N.State) (i : N.Inputs) :
  R.v5896 (state s) (inputs i) = Zmod.unsigned (N.v5896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5896 s i)) at 1.
  unfold R.v5896, N.v5896.
  rewrite ?node_5831.
  rewrite !state_r177_nr_5F177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r177_nr_5F177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5897 (s : N.State) (i : N.Inputs) :
  R.v5897 (state s) (inputs i) = Zmod.unsigned (N.v5897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5897 s i)) at 1.
  unfold R.v5897, N.v5897.
  rewrite ?node_5895.
  rewrite ?node_5896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5898 (s : N.State) (i : N.Inputs) :
  R.v5898 (state s) (inputs i) = Zmod.unsigned (N.v5898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5898 s i)) at 1.
  unfold R.v5898, N.v5898.
  rewrite ?node_5894.
  rewrite ?node_5897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5899 (s : N.State) (i : N.Inputs) :
  R.v5899 (state s) (inputs i) = Zmod.unsigned (N.v5899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5899 s i)) at 1.
  unfold R.v5899, N.v5899.
  rewrite ?node_5891.
  rewrite ?node_5898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5900 (s : N.State) (i : N.Inputs) :
  R.v5900 (state s) (inputs i) = Zmod.unsigned (N.v5900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5900 s i)) at 1.
  unfold R.v5900, N.v5900.
  rewrite !state_r192_nr_5F192.
  rewrite !state_r193_nr_5F193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r192_nr_5F192 s)).
  rewrite ?(bits.mod_to_Z (N.r193_nr_5F193 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5901 (s : N.State) (i : N.Inputs) :
  R.v5901 (state s) (inputs i) = Zmod.unsigned (N.v5901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5901 s i)) at 1.
  unfold R.v5901, N.v5901.
  rewrite ?node_5899.
  rewrite ?node_5900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5902 (s : N.State) (i : N.Inputs) :
  R.v5902 (state s) (inputs i) = Zmod.unsigned (N.v5902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5902 s i)) at 1.
  unfold R.v5902, N.v5902.
  rewrite ?node_5822.
  rewrite ?node_5829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5903 (s : N.State) (i : N.Inputs) :
  R.v5903 (state s) (inputs i) = Zmod.unsigned (N.v5903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5903 s i)) at 1.
  unfold R.v5903, N.v5903.
  rewrite ?node_5830.
  rewrite ?node_5837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5904 (s : N.State) (i : N.Inputs) :
  R.v5904 (state s) (inputs i) = Zmod.unsigned (N.v5904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5904 s i)) at 1.
  unfold R.v5904, N.v5904.
  rewrite ?node_5902.
  rewrite ?node_5903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5905 (s : N.State) (i : N.Inputs) :
  R.v5905 (state s) (inputs i) = Zmod.unsigned (N.v5905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5905 s i)) at 1.
  unfold R.v5905, N.v5905.
  rewrite ?node_5901.
  rewrite ?node_5904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5906 (s : N.State) (i : N.Inputs) :
  R.v5906 (state s) (inputs i) = Zmod.unsigned (N.v5906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5906 s i)) at 1.
  unfold R.v5906, N.v5906.
  rewrite ?node_5817.
  rewrite !state_r170_nr_5F170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r170_nr_5F170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5907 (s : N.State) (i : N.Inputs) :
  R.v5907 (state s) (inputs i) = Zmod.unsigned (N.v5907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5907 s i)) at 1.
  unfold R.v5907, N.v5907.
  rewrite ?node_5818.
  rewrite ?node_5821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5908 (s : N.State) (i : N.Inputs) :
  R.v5908 (state s) (inputs i) = Zmod.unsigned (N.v5908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5908 s i)) at 1.
  unfold R.v5908, N.v5908.
  rewrite ?node_5906.
  rewrite ?node_5907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5909 (s : N.State) (i : N.Inputs) :
  R.v5909 (state s) (inputs i) = Zmod.unsigned (N.v5909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5909 s i)) at 1.
  unfold R.v5909, N.v5909.
  rewrite ?node_5824.
  rewrite !state_r174_nr_5F174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r174_nr_5F174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5910 (s : N.State) (i : N.Inputs) :
  R.v5910 (state s) (inputs i) = Zmod.unsigned (N.v5910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5910 s i)) at 1.
  unfold R.v5910, N.v5910.
  rewrite ?node_5825.
  rewrite ?node_5828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5911 (s : N.State) (i : N.Inputs) :
  R.v5911 (state s) (inputs i) = Zmod.unsigned (N.v5911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5911 s i)) at 1.
  unfold R.v5911, N.v5911.
  rewrite ?node_5909.
  rewrite ?node_5910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5912 (s : N.State) (i : N.Inputs) :
  R.v5912 (state s) (inputs i) = Zmod.unsigned (N.v5912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5912 s i)) at 1.
  unfold R.v5912, N.v5912.
  rewrite ?node_5908.
  rewrite ?node_5911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5913 (s : N.State) (i : N.Inputs) :
  R.v5913 (state s) (inputs i) = Zmod.unsigned (N.v5913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5913 s i)) at 1.
  unfold R.v5913, N.v5913.
  rewrite ?node_5832.
  rewrite !state_r178_nr_5F178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r178_nr_5F178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5914 (s : N.State) (i : N.Inputs) :
  R.v5914 (state s) (inputs i) = Zmod.unsigned (N.v5914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5914 s i)) at 1.
  unfold R.v5914, N.v5914.
  rewrite ?node_5833.
  rewrite ?node_5836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5915 (s : N.State) (i : N.Inputs) :
  R.v5915 (state s) (inputs i) = Zmod.unsigned (N.v5915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5915 s i)) at 1.
  unfold R.v5915, N.v5915.
  rewrite ?node_5913.
  rewrite ?node_5914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5916 (s : N.State) (i : N.Inputs) :
  R.v5916 (state s) (inputs i) = Zmod.unsigned (N.v5916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5916 s i)) at 1.
  unfold R.v5916, N.v5916.
  rewrite ?node_5912.
  rewrite ?node_5915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5917 (s : N.State) (i : N.Inputs) :
  R.v5917 (state s) (inputs i) = Zmod.unsigned (N.v5917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5917 s i)) at 1.
  unfold R.v5917, N.v5917.
  rewrite ?node_5905.
  rewrite ?node_5916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5918 (s : N.State) (i : N.Inputs) :
  R.v5918 (state s) (inputs i) = Zmod.unsigned (N.v5918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5918 s i)) at 1.
  unfold R.v5918, N.v5918.
  rewrite ?node_5838.
  rewrite !state_r179_nr_5F179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r179_nr_5F179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5919 (s : N.State) (i : N.Inputs) :
  R.v5919 (state s) (inputs i) = Zmod.unsigned (N.v5919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5919 s i)) at 1.
  unfold R.v5919, N.v5919.
  rewrite ?node_5839.
  rewrite ?node_5842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5920 (s : N.State) (i : N.Inputs) :
  R.v5920 (state s) (inputs i) = Zmod.unsigned (N.v5920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5920 s i)) at 1.
  unfold R.v5920, N.v5920.
  rewrite ?node_5918.
  rewrite ?node_5919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5921 (s : N.State) (i : N.Inputs) :
  R.v5921 (state s) (inputs i) = Zmod.unsigned (N.v5921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5921 s i)) at 1.
  unfold R.v5921, N.v5921.
  rewrite ?node_5917.
  rewrite ?node_5920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5922 (s : N.State) (i : N.Inputs) :
  R.v5922 (state s) (inputs i) = Zmod.unsigned (N.v5922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5922 s i)) at 1.
  unfold R.v5922, N.v5922.
  rewrite ?node_5846.
  rewrite ?node_5849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5923 (s : N.State) (i : N.Inputs) :
  R.v5923 (state s) (inputs i) = Zmod.unsigned (N.v5923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5923 s i)) at 1.
  unfold R.v5923, N.v5923.
  rewrite ?node_5850.
  rewrite ?node_5853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5924 (s : N.State) (i : N.Inputs) :
  R.v5924 (state s) (inputs i) = Zmod.unsigned (N.v5924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5924 s i)) at 1.
  unfold R.v5924, N.v5924.
  rewrite ?node_5922.
  rewrite ?node_5923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5925 (s : N.State) (i : N.Inputs) :
  R.v5925 (state s) (inputs i) = Zmod.unsigned (N.v5925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5925 s i)) at 1.
  unfold R.v5925, N.v5925.
  rewrite ?node_5921.
  rewrite ?node_5924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5926 (s : N.State) (i : N.Inputs) :
  R.v5926 (state s) (inputs i) = Zmod.unsigned (N.v5926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5926 s i)) at 1.
  unfold R.v5926, N.v5926.
  rewrite ?node_5843.
  rewrite ?node_5854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5927 (s : N.State) (i : N.Inputs) :
  R.v5927 (state s) (inputs i) = Zmod.unsigned (N.v5927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5927 s i)) at 1.
  unfold R.v5927, N.v5927.
  rewrite ?node_5855.
  rewrite ?node_5858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5928 (s : N.State) (i : N.Inputs) :
  R.v5928 (state s) (inputs i) = Zmod.unsigned (N.v5928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5928 s i)) at 1.
  unfold R.v5928, N.v5928.
  rewrite ?node_5926.
  rewrite ?node_5927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5929 (s : N.State) (i : N.Inputs) :
  R.v5929 (state s) (inputs i) = Zmod.unsigned (N.v5929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5929 s i)) at 1.
  unfold R.v5929, N.v5929.
  rewrite ?node_5925.
  rewrite ?node_5928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5930 (s : N.State) (i : N.Inputs) :
  R.v5930 (state s) (inputs i) = Zmod.unsigned (N.v5930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5930 s i)) at 1.
  unfold R.v5930, N.v5930.
  rewrite ?node_5859.
  rewrite ?node_5862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5931 (s : N.State) (i : N.Inputs) :
  R.v5931 (state s) (inputs i) = Zmod.unsigned (N.v5931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5931 s i)) at 1.
  unfold R.v5931, N.v5931.
  rewrite ?node_5863.
  rewrite ?node_5866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5932 (s : N.State) (i : N.Inputs) :
  R.v5932 (state s) (inputs i) = Zmod.unsigned (N.v5932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5932 s i)) at 1.
  unfold R.v5932, N.v5932.
  rewrite ?node_5930.
  rewrite ?node_5931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5933 (s : N.State) (i : N.Inputs) :
  R.v5933 (state s) (inputs i) = Zmod.unsigned (N.v5933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5933 s i)) at 1.
  unfold R.v5933, N.v5933.
  rewrite ?node_5929.
  rewrite ?node_5932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5934 (s : N.State) (i : N.Inputs) :
  R.v5934 (state s) (inputs i) = Zmod.unsigned (N.v5934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5934 s i)) at 1.
  unfold R.v5934, N.v5934.
  rewrite ?node_5867.
  rewrite ?node_5870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5935 (s : N.State) (i : N.Inputs) :
  R.v5935 (state s) (inputs i) = Zmod.unsigned (N.v5935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5935 s i)) at 1.
  unfold R.v5935, N.v5935.
  rewrite ?node_5933.
  rewrite ?node_5934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5936 (s : N.State) (i : N.Inputs) :
  R.v5936 (state s) (inputs i) = Zmod.unsigned (N.v5936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5936 s i)) at 1.
  unfold R.v5936, N.v5936.
  rewrite ?node_5935.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2321_nr_5F2352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2321_nr_5F2352 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5937 (s : N.State) (i : N.Inputs) :
  R.v5937 (state s) (inputs i) = Zmod.unsigned (N.v5937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5937 s i)) at 1.
  unfold R.v5937, N.v5937.
  rewrite ?node_5871.
  rewrite ?node_5872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5938 (s : N.State) (i : N.Inputs) :
  R.v5938 (state s) (inputs i) = Zmod.unsigned (N.v5938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5938 s i)) at 1.
  unfold R.v5938, N.v5938.
  rewrite ?node_5937.
  rewrite !inputs_nio_5FregEnables_5F1.
  rewrite !state_r2322_nr_5F2353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F1 i)).
  rewrite ?(bits.mod_to_Z (N.r2322_nr_5F2353 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5939 (s : N.State) (i : N.Inputs) :
  R.v5939 (state s) (inputs i) = Zmod.unsigned (N.v5939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5939 s i)) at 1.
  unfold R.v5939, N.v5939.
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

Lemma node_5940 (s : N.State) (i : N.Inputs) :
  R.v5940 (state s) (inputs i) = Zmod.unsigned (N.v5940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5940 s i)) at 1.
  unfold R.v5940, N.v5940.
  rewrite ?node_5939.
  rewrite !state_r196_nr_5F196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r196_nr_5F196 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5941 (s : N.State) (i : N.Inputs) :
  R.v5941 (state s) (inputs i) = Zmod.unsigned (N.v5941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5941 s i)) at 1.
  unfold R.v5941, N.v5941.
  rewrite ?node_5940.
  rewrite !state_r197_nr_5F197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r197_nr_5F197 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5942 (s : N.State) (i : N.Inputs) :
  R.v5942 (state s) (inputs i) = Zmod.unsigned (N.v5942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5942 s i)) at 1.
  unfold R.v5942, N.v5942.
  rewrite !state_r180_nr_5F180.
  rewrite !state_r181_nr_5F181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r180_nr_5F180 s)).
  rewrite ?(bits.mod_to_Z (N.r181_nr_5F181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5943 (s : N.State) (i : N.Inputs) :
  R.v5943 (state s) (inputs i) = Zmod.unsigned (N.v5943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5943 s i)) at 1.
  unfold R.v5943, N.v5943.
  rewrite ?node_5877.
  rewrite !state_r182_nr_5F182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r182_nr_5F182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5944 (s : N.State) (i : N.Inputs) :
  R.v5944 (state s) (inputs i) = Zmod.unsigned (N.v5944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5944 s i)) at 1.
  unfold R.v5944, N.v5944.
  rewrite ?node_5942.
  rewrite ?node_5943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5945 (s : N.State) (i : N.Inputs) :
  R.v5945 (state s) (inputs i) = Zmod.unsigned (N.v5945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5945 s i)) at 1.
  unfold R.v5945, N.v5945.
  rewrite ?node_5941.
  rewrite ?node_5944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5946 (s : N.State) (i : N.Inputs) :
  R.v5946 (state s) (inputs i) = Zmod.unsigned (N.v5946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5946 s i)) at 1.
  unfold R.v5946, N.v5946.
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

Lemma node_5947 (s : N.State) (i : N.Inputs) :
  R.v5947 (state s) (inputs i) = Zmod.unsigned (N.v5947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5947 s i)) at 1.
  unfold R.v5947, N.v5947.
  rewrite ?node_5946.
  rewrite !state_r200_nr_5F200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r200_nr_5F200 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5948 (s : N.State) (i : N.Inputs) :
  R.v5948 (state s) (inputs i) = Zmod.unsigned (N.v5948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5948 s i)) at 1.
  unfold R.v5948, N.v5948.
  rewrite ?node_5947.
  rewrite !state_r201_nr_5F201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r201_nr_5F201 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5949 (s : N.State) (i : N.Inputs) :
  R.v5949 (state s) (inputs i) = Zmod.unsigned (N.v5949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5949 s i)) at 1.
  unfold R.v5949, N.v5949.
  rewrite !state_r184_nr_5F184.
  rewrite !state_r185_nr_5F185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r184_nr_5F184 s)).
  rewrite ?(bits.mod_to_Z (N.r185_nr_5F185 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5950 (s : N.State) (i : N.Inputs) :
  R.v5950 (state s) (inputs i) = Zmod.unsigned (N.v5950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5950 s i)) at 1.
  unfold R.v5950, N.v5950.
  rewrite ?node_5884.
  rewrite !state_r186_nr_5F186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r186_nr_5F186 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5951 (s : N.State) (i : N.Inputs) :
  R.v5951 (state s) (inputs i) = Zmod.unsigned (N.v5951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5951 s i)) at 1.
  unfold R.v5951, N.v5951.
  rewrite ?node_5949.
  rewrite ?node_5950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5952 (s : N.State) (i : N.Inputs) :
  R.v5952 (state s) (inputs i) = Zmod.unsigned (N.v5952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5952 s i)) at 1.
  unfold R.v5952, N.v5952.
  rewrite ?node_5948.
  rewrite ?node_5951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5953 (s : N.State) (i : N.Inputs) :
  R.v5953 (state s) (inputs i) = Zmod.unsigned (N.v5953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5953 s i)) at 1.
  unfold R.v5953, N.v5953.
  rewrite ?node_5945.
  rewrite ?node_5952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5954 (s : N.State) (i : N.Inputs) :
  R.v5954 (state s) (inputs i) = Zmod.unsigned (N.v5954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5954 s i)) at 1.
  unfold R.v5954, N.v5954.
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

Lemma node_5955 (s : N.State) (i : N.Inputs) :
  R.v5955 (state s) (inputs i) = Zmod.unsigned (N.v5955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5955 s i)) at 1.
  unfold R.v5955, N.v5955.
  rewrite ?node_5954.
  rewrite !state_r204_nr_5F204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r204_nr_5F204 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5956 (s : N.State) (i : N.Inputs) :
  R.v5956 (state s) (inputs i) = Zmod.unsigned (N.v5956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5956 s i)) at 1.
  unfold R.v5956, N.v5956.
  rewrite ?node_5955.
  rewrite !state_r205_nr_5F205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r205_nr_5F205 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5957 (s : N.State) (i : N.Inputs) :
  R.v5957 (state s) (inputs i) = Zmod.unsigned (N.v5957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5957 s i)) at 1.
  unfold R.v5957, N.v5957.
  rewrite !state_r188_nr_5F188.
  rewrite !state_r189_nr_5F189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r188_nr_5F188 s)).
  rewrite ?(bits.mod_to_Z (N.r189_nr_5F189 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5958 (s : N.State) (i : N.Inputs) :
  R.v5958 (state s) (inputs i) = Zmod.unsigned (N.v5958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5958 s i)) at 1.
  unfold R.v5958, N.v5958.
  rewrite ?node_5892.
  rewrite !state_r190_nr_5F190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r190_nr_5F190 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5959 (s : N.State) (i : N.Inputs) :
  R.v5959 (state s) (inputs i) = Zmod.unsigned (N.v5959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5959 s i)) at 1.
  unfold R.v5959, N.v5959.
  rewrite ?node_5957.
  rewrite ?node_5958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5960 (s : N.State) (i : N.Inputs) :
  R.v5960 (state s) (inputs i) = Zmod.unsigned (N.v5960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5960 s i)) at 1.
  unfold R.v5960, N.v5960.
  rewrite ?node_5956.
  rewrite ?node_5959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5961 (s : N.State) (i : N.Inputs) :
  R.v5961 (state s) (inputs i) = Zmod.unsigned (N.v5961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5961 s i)) at 1.
  unfold R.v5961, N.v5961.
  rewrite ?node_5953.
  rewrite ?node_5960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5962 (s : N.State) (i : N.Inputs) :
  R.v5962 (state s) (inputs i) = Zmod.unsigned (N.v5962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5962 s i)) at 1.
  unfold R.v5962, N.v5962.
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

Lemma node_5963 (s : N.State) (i : N.Inputs) :
  R.v5963 (state s) (inputs i) = Zmod.unsigned (N.v5963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5963 s i)) at 1.
  unfold R.v5963, N.v5963.
  rewrite ?node_5961.
  rewrite ?node_5962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5964 (s : N.State) (i : N.Inputs) :
  R.v5964 (state s) (inputs i) = Zmod.unsigned (N.v5964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5964 s i)) at 1.
  unfold R.v5964, N.v5964.
  rewrite ?node_5883.
  rewrite ?node_5890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5965 (s : N.State) (i : N.Inputs) :
  R.v5965 (state s) (inputs i) = Zmod.unsigned (N.v5965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5965 s i)) at 1.
  unfold R.v5965, N.v5965.
  rewrite ?node_5891.
  rewrite ?node_5898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5966 (s : N.State) (i : N.Inputs) :
  R.v5966 (state s) (inputs i) = Zmod.unsigned (N.v5966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5966 s i)) at 1.
  unfold R.v5966, N.v5966.
  rewrite ?node_5964.
  rewrite ?node_5965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5967 (s : N.State) (i : N.Inputs) :
  R.v5967 (state s) (inputs i) = Zmod.unsigned (N.v5967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5967 s i)) at 1.
  unfold R.v5967, N.v5967.
  rewrite ?node_5963.
  rewrite ?node_5966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5968 (s : N.State) (i : N.Inputs) :
  R.v5968 (state s) (inputs i) = Zmod.unsigned (N.v5968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5968 s i)) at 1.
  unfold R.v5968, N.v5968.
  rewrite ?node_5878.
  rewrite !state_r183_nr_5F183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r183_nr_5F183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5969 (s : N.State) (i : N.Inputs) :
  R.v5969 (state s) (inputs i) = Zmod.unsigned (N.v5969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5969 s i)) at 1.
  unfold R.v5969, N.v5969.
  rewrite ?node_5879.
  rewrite ?node_5882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5970 (s : N.State) (i : N.Inputs) :
  R.v5970 (state s) (inputs i) = Zmod.unsigned (N.v5970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5970 s i)) at 1.
  unfold R.v5970, N.v5970.
  rewrite ?node_5968.
  rewrite ?node_5969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5971 (s : N.State) (i : N.Inputs) :
  R.v5971 (state s) (inputs i) = Zmod.unsigned (N.v5971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5971 s i)) at 1.
  unfold R.v5971, N.v5971.
  rewrite ?node_5885.
  rewrite !state_r187_nr_5F187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r187_nr_5F187 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5972 (s : N.State) (i : N.Inputs) :
  R.v5972 (state s) (inputs i) = Zmod.unsigned (N.v5972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5972 s i)) at 1.
  unfold R.v5972, N.v5972.
  rewrite ?node_5886.
  rewrite ?node_5889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5973 (s : N.State) (i : N.Inputs) :
  R.v5973 (state s) (inputs i) = Zmod.unsigned (N.v5973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5973 s i)) at 1.
  unfold R.v5973, N.v5973.
  rewrite ?node_5971.
  rewrite ?node_5972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5974 (s : N.State) (i : N.Inputs) :
  R.v5974 (state s) (inputs i) = Zmod.unsigned (N.v5974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5974 s i)) at 1.
  unfold R.v5974, N.v5974.
  rewrite ?node_5970.
  rewrite ?node_5973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5975 (s : N.State) (i : N.Inputs) :
  R.v5975 (state s) (inputs i) = Zmod.unsigned (N.v5975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5975 s i)) at 1.
  unfold R.v5975, N.v5975.
  rewrite ?node_5893.
  rewrite !state_r191_nr_5F191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r191_nr_5F191 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5976 (s : N.State) (i : N.Inputs) :
  R.v5976 (state s) (inputs i) = Zmod.unsigned (N.v5976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5976 s i)) at 1.
  unfold R.v5976, N.v5976.
  rewrite ?node_5894.
  rewrite ?node_5897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5977 (s : N.State) (i : N.Inputs) :
  R.v5977 (state s) (inputs i) = Zmod.unsigned (N.v5977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5977 s i)) at 1.
  unfold R.v5977, N.v5977.
  rewrite ?node_5975.
  rewrite ?node_5976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5978 (s : N.State) (i : N.Inputs) :
  R.v5978 (state s) (inputs i) = Zmod.unsigned (N.v5978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5978 s i)) at 1.
  unfold R.v5978, N.v5978.
  rewrite ?node_5974.
  rewrite ?node_5977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5979 (s : N.State) (i : N.Inputs) :
  R.v5979 (state s) (inputs i) = Zmod.unsigned (N.v5979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5979 s i)) at 1.
  unfold R.v5979, N.v5979.
  rewrite !state_r192_nr_5F192.
  rewrite !state_r193_nr_5F193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r192_nr_5F192 s)).
  rewrite ?(bits.mod_to_Z (N.r193_nr_5F193 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5980 (s : N.State) (i : N.Inputs) :
  R.v5980 (state s) (inputs i) = Zmod.unsigned (N.v5980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5980 s i)) at 1.
  unfold R.v5980, N.v5980.
  rewrite ?node_5978.
  rewrite ?node_5979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5981 (s : N.State) (i : N.Inputs) :
  R.v5981 (state s) (inputs i) = Zmod.unsigned (N.v5981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5981 s i)) at 1.
  unfold R.v5981, N.v5981.
  rewrite ?node_5967.
  rewrite ?node_5980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5982 (s : N.State) (i : N.Inputs) :
  R.v5982 (state s) (inputs i) = Zmod.unsigned (N.v5982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5982 s i)) at 1.
  unfold R.v5982, N.v5982.
  rewrite ?node_5899.
  rewrite ?node_5900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5983 (s : N.State) (i : N.Inputs) :
  R.v5983 (state s) (inputs i) = Zmod.unsigned (N.v5983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5983 s i)) at 1.
  unfold R.v5983, N.v5983.
  rewrite ?node_5901.
  rewrite ?node_5904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5984 (s : N.State) (i : N.Inputs) :
  R.v5984 (state s) (inputs i) = Zmod.unsigned (N.v5984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5984 s i)) at 1.
  unfold R.v5984, N.v5984.
  rewrite ?node_5982.
  rewrite ?node_5983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5985 (s : N.State) (i : N.Inputs) :
  R.v5985 (state s) (inputs i) = Zmod.unsigned (N.v5985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5985 s i)) at 1.
  unfold R.v5985, N.v5985.
  rewrite ?node_5981.
  rewrite ?node_5984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5986 (s : N.State) (i : N.Inputs) :
  R.v5986 (state s) (inputs i) = Zmod.unsigned (N.v5986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5986 s i)) at 1.
  unfold R.v5986, N.v5986.
  rewrite ?node_5908.
  rewrite ?node_5911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5987 (s : N.State) (i : N.Inputs) :
  R.v5987 (state s) (inputs i) = Zmod.unsigned (N.v5987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5987 s i)) at 1.
  unfold R.v5987, N.v5987.
  rewrite ?node_5912.
  rewrite ?node_5915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5988 (s : N.State) (i : N.Inputs) :
  R.v5988 (state s) (inputs i) = Zmod.unsigned (N.v5988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5988 s i)) at 1.
  unfold R.v5988, N.v5988.
  rewrite ?node_5986.
  rewrite ?node_5987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5989 (s : N.State) (i : N.Inputs) :
  R.v5989 (state s) (inputs i) = Zmod.unsigned (N.v5989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5989 s i)) at 1.
  unfold R.v5989, N.v5989.
  rewrite ?node_5985.
  rewrite ?node_5988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5990 (s : N.State) (i : N.Inputs) :
  R.v5990 (state s) (inputs i) = Zmod.unsigned (N.v5990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5990 s i)) at 1.
  unfold R.v5990, N.v5990.
  rewrite ?node_5905.
  rewrite ?node_5916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5991 (s : N.State) (i : N.Inputs) :
  R.v5991 (state s) (inputs i) = Zmod.unsigned (N.v5991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5991 s i)) at 1.
  unfold R.v5991, N.v5991.
  rewrite ?node_5917.
  rewrite ?node_5920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5992 (s : N.State) (i : N.Inputs) :
  R.v5992 (state s) (inputs i) = Zmod.unsigned (N.v5992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5992 s i)) at 1.
  unfold R.v5992, N.v5992.
  rewrite ?node_5990.
  rewrite ?node_5991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5993 (s : N.State) (i : N.Inputs) :
  R.v5993 (state s) (inputs i) = Zmod.unsigned (N.v5993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5993 s i)) at 1.
  unfold R.v5993, N.v5993.
  rewrite ?node_5989.
  rewrite ?node_5992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5994 (s : N.State) (i : N.Inputs) :
  R.v5994 (state s) (inputs i) = Zmod.unsigned (N.v5994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5994 s i)) at 1.
  unfold R.v5994, N.v5994.
  rewrite ?node_5921.
  rewrite ?node_5924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5995 (s : N.State) (i : N.Inputs) :
  R.v5995 (state s) (inputs i) = Zmod.unsigned (N.v5995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5995 s i)) at 1.
  unfold R.v5995, N.v5995.
  rewrite ?node_5925.
  rewrite ?node_5928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5996 (s : N.State) (i : N.Inputs) :
  R.v5996 (state s) (inputs i) = Zmod.unsigned (N.v5996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5996 s i)) at 1.
  unfold R.v5996, N.v5996.
  rewrite ?node_5994.
  rewrite ?node_5995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5997 (s : N.State) (i : N.Inputs) :
  R.v5997 (state s) (inputs i) = Zmod.unsigned (N.v5997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5997 s i)) at 1.
  unfold R.v5997, N.v5997.
  rewrite ?node_5993.
  rewrite ?node_5996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5998 (s : N.State) (i : N.Inputs) :
  R.v5998 (state s) (inputs i) = Zmod.unsigned (N.v5998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5998 s i)) at 1.
  unfold R.v5998, N.v5998.
  rewrite ?node_5929.
  rewrite ?node_5932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5999 (s : N.State) (i : N.Inputs) :
  R.v5999 (state s) (inputs i) = Zmod.unsigned (N.v5999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5999 s i)) at 1.
  unfold R.v5999, N.v5999.
  rewrite ?node_5997.
  rewrite ?node_5998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
